import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms

set_option doc.verso.suggestions false

/-!
# 分析学 I, 第4.1节: 整数

本节的主要构造和结果：

- 将"第4.1节"整数 `Section_4_1.Int` 定义为自然数 `a b:ℕ` 的形式差 `a —— b`，直到等价。
  （这是脚手架类型 `Section_4_1.PreInt` 的商，`PreInt` 由不施加任何等价关系的形式差组成。）

- 这些整数的环运算和序，以及 ℕ 的嵌入。

- 与 Mathlib 整数 {name}`_root_.Int`（或 {lean}`ℤ`）的等价，我们将在后续继续使用。

## 来自以往用户的提示

完成本节习题的用户欢迎发送他们对本节未来用户的提示作为 PRs。
-/

namespace Section_4_1

structure PreInt where
  minuend : ℕ
  subtrahend : ℕ

/-- 定义 4.1.1 -/
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := {
    refl := by intro; rfl          -- 自反性：a + b = a + b
    symm := by intro x y h; rw [h] -- 对称性
    trans := by
      -- 此证明按原文结构书写
      intro ⟨ a,b ⟩ ⟨ c,d ⟩ ⟨ e,f ⟩ h1 h2; simp_all
      have h3 := congrArg₂ (· + ·) h1 h2; simp at h3
      have : (a + f) + (c + d) = (e + b) + (c + d) := calc
        (a + f) + (c + d) = a + d + (c + f) := by abel
        _ = c + b + (e + d) := h3
        _ = (e + b) + (c + d) := by abel
      exact Nat.add_right_cancel this
  }

@[simp]
theorem PreInt.eq (a b c d:ℕ) : (⟨ a,b ⟩: PreInt) ≈ ⟨ c,d ⟩ ↔ a + d = c + b := by rfl

abbrev Int := Quotient PreInt.instSetoid

abbrev Int.formalDiff (a b:ℕ)  : Int := Quotient.mk PreInt.instSetoid ⟨ a,b ⟩

infix:100 " —— " => Int.formalDiff

/-- 定义 4.1.1（整数） -/
theorem Int.eq (a b c d:ℕ): a —— b = c —— d ↔ a + d = c + b :=
  ⟨ Quotient.exact, by intro h; exact Quotient.sound h ⟩

/-- 整数相等的可判定性 -/
instance Int.decidableEq : DecidableEq Int := by
  intro a b
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n = Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    rw [eq]
    exact decEq _ _
  exact Quotient.recOnSubsingleton₂ a b this

/-- 定义 4.1.1（整数）：每个整数都可以表示为形式差 -/
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b := by apply n.ind _; intro ⟨ a, b ⟩; use a, b

/-- 引理 4.1.3（加法良好定义） -/
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a+c) —— (b+d) ) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    simp [eq] at *
    omega)

/-- 定义 4.1.2（加法定义） -/
theorem Int.add_eq (a b c d:ℕ) : a —— b + c —— d = (a+c)——(b+d) := Quotient.lift₂_mk _ _ _ _

/-- 引理 4.1.3（乘法良好定义）：左相等 -/
theorem Int.mul_congr_left (a b a' b' c d : ℕ) (h: a —— b = a' —— b') :
    (a*c+b*d) —— (a*d+b*c) = (a'*c+b'*d) —— (a'*d+b'*c) := by
  simp only [eq] at *
  calc
    _ = c*(a+b') + d*(a'+b) := by ring
    _ = c*(a'+b) + d*(a+b') := by rw [h]
    _ = _ := by ring

/-- 引理 4.1.3（乘法良好定义）：右相等 -/
theorem Int.mul_congr_right (a b c d c' d' : ℕ) (h: c —— d = c' —— d') :
    (a*c+b*d) —— (a*d+b*c) = (a*c'+b*d') —— (a*d'+b*c') := by
  simp only [eq] at *
  calc
    _ = a*(c+d') + b*(c'+d) := by ring
    _ = a*(c'+d) + b*(c+d') := by rw [h]
    _ = _ := by ring

/-- 引理 4.1.3（乘法良好定义）：右相等 -/
theorem Int.mul_congr {a b c d a' b' c' d' : ℕ} (h1: a —— b = a' —— b') (h2: c —— d = c' —— d') :
  (a*c+b*d) —— (a*d+b*c) = (a'*c'+b'*d') —— (a'*d'+b'*c') := by
  rw [mul_congr_left a b a' b' c d h1, mul_congr_right a' b' c d c' d' h2]

instance Int.instMul : Mul Int where
  mul := Quotient.lift₂ (fun ⟨ a, b ⟩ ⟨ c, d ⟩ ↦ (a * c + b * d) —— (a * d + b * c)) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ ⟨ a', b' ⟩ ⟨ c', d' ⟩ h1 h2
    exact mul_congr (Quotient.eq.mpr h1) (Quotient.eq.mpr h2)
    )

/-- 定义 4.1.2（整数乘法） -/
theorem Int.mul_eq (a b c d:ℕ) : a —— b * c —— d = (a*c+b*d) —— (a*d+b*c) := Quotient.lift₂_mk _ _ _ _

-- natural numbers as integers
instance Int.instOfNat {n:ℕ} : OfNat Int n where
  ofNat := n —— 0

-- 定义 4.1.2（自然数作为整数） -/
instance Int.instNatCast : NatCast Int where
  natCast n := n —— 0

theorem Int.ofNat_eq (n:ℕ) : ofNat(n) = n —— 0 := rfl

theorem Int.natCast_eq (n:ℕ) : (n:Int) = n —— 0 := rfl

-- 自然数转自然数再转整数等于自然数转整数
@[simp]
theorem Int.natCast_ofNat (n:ℕ) : ((ofNat(n):ℕ): Int) = ofNat(n) := by rfl

-- 自然数转整数相等， 等价于自然数相等
@[simp]
theorem Int.ofNat_inj (n m:ℕ) : (ofNat(n) : Int) = (ofNat(m) : Int) ↔ ofNat(n) = ofNat(m) := by
  simp only [ofNat_eq, eq, add_zero]; rfl

-- 自然数转整数相等， 等价于自然数相等
@[simp]
theorem Int.natCast_inj (n m:ℕ) : (n : Int) = (m : Int) ↔ n = m := by
  simp only [natCast_eq, eq, add_zero]

example : 3 = 3 —— 0 := rfl

example : 3 = 4 —— 1 := by rw [Int.ofNat_eq, Int.eq]

/--（不在教科书中）0 是唯一其类型转换后为 0 的自然数 -/
lemma Int.cast_eq_0_iff_eq_0 (n : ℕ) : (n : Int) = 0 ↔ n = 0 := by
  have : 0 = 0 —— 0 := rfl
  simp only [natCast_eq, this, eq, add_zero]

/-- 定义 4.1.4（整数的否定）/ 习题 4.1.2 -/
instance Int.instNeg : Neg Int where
  neg := Quotient.lift (fun ⟨ a, b ⟩ ↦ b —— a) (by
    intro ⟨ a, b ⟩ ⟨ c, d ⟩ h
    simp only [eq] at *
    rw [add_comm, add_comm d, eq_comm]
    omega)

theorem Int.neg_eq (a b:ℕ) : -(a —— b) = b —— a := rfl

example : -(3 —— 5) = 5 —— 3 := rfl

abbrev Int.IsPos (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = n
abbrev Int.IsNeg (x:Int) : Prop := ∃ (n:ℕ), n > 0 ∧ x = -n

/-- 引理 4.1.5（整数的三歧性） -/
theorem Int.trichotomous (x:Int) : x = 0 ∨ x.IsPos ∨ x.IsNeg := by
  -- 此证明略有修改
  obtain ⟨ a, b, rfl ⟩ := eq_diff x
  obtain h_lt | rfl | h_gt := _root_.trichotomous (r := LT.lt) a b
  . obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_lt
    right; right; refine ⟨ c+1, by linarith, ?_ ⟩
    simp_rw [natCast_eq, neg_eq, eq, zero_add, add_assoc]
  . left; simp_rw [ofNat_eq, eq, add_zero, zero_add]
  obtain ⟨ c, rfl ⟩ := Nat.exists_eq_add_of_lt h_gt
  right; left; refine ⟨ c+1, by linarith, ?_ ⟩
  simp_rw [natCast_eq, eq]; abel

/-- 引理 4.1.5（整数的三歧性） -/
theorem Int.not_pos_zero (x:Int) : x = 0 ∧ x.IsPos → False := by
  rintro ⟨ rfl, ⟨ n, _, _ ⟩ ⟩; simp_all [←natCast_ofNat]

/-- 引理 4.1.5（整数的三歧性） -/
theorem Int.not_neg_zero (x:Int) : x = 0 ∧ x.IsNeg → False := by
  rintro ⟨ rfl, ⟨ n, _, hn ⟩ ⟩; simp_rw [←natCast_ofNat, natCast_eq, neg_eq, eq] at hn
  linarith

/-- 引理 4.1.5（整数的三歧性） -/
theorem Int.not_pos_neg (x:Int) : x.IsPos ∧ x.IsNeg → False := by
  rintro ⟨ ⟨ n, _, rfl ⟩, ⟨ m, _, hm ⟩ ⟩; simp_rw [natCast_eq, neg_eq, eq] at hm
  linarith

/-- 命题 4.1.6（代数定律）/ 习题 4.1.4 -/
instance Int.instAddGroup : AddGroup Int :=
  AddGroup.ofLeftAxioms (by
    -- ⊢ ∀ (a b c : Int), a + b + c = a + (b + c)
    intro a b c
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
    obtain ⟨ c1, c2, rfl ⟩ := eq_diff c
    simp_rw [add_eq, add_assoc]
  ) (by
    -- ⊢ ∀ (a : Int), 0 + a = a
    intro a; obtain ⟨ a1, a2, rfl ⟩ := eq_diff a;
    have : 0 = 0 —— 0 := rfl
    simp_rw [this, add_eq, zero_add]
  ) (by
    -- ⊢ ∀ (a : Int), -a + a = 0
    intro a; obtain ⟨ a1, a2, rfl ⟩ := eq_diff a;
    have : 0 = 0 —— 0 := rfl
    simp_rw [neg_eq, add_eq, add_comm, this, Int.eq, add_zero, zero_add]
  )

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instAddCommGroup : AddCommGroup Int where
  add_comm := by
    intro a b
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
    simp_rw [add_eq, add_comm]

/-- Proposition 4.1.6 (laws of algebra) / Exercise 4.1.4 -/
instance Int.instCommMonoid : CommMonoid Int where
  mul_comm := by
    intro a b
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
    simp_rw [mul_eq,mul_comm, add_comm]
  mul_assoc := by
    -- 此证明按原文结构书写
    intro x y z
    obtain ⟨ a, b, rfl ⟩ := eq_diff x
    obtain ⟨ c, d, rfl ⟩ := eq_diff y
    obtain ⟨ e, f, rfl ⟩ := eq_diff z
    simp_rw [mul_eq]; congr 1 <;> ring
  one_mul := by
    intro a; obtain ⟨ a1, a2, rfl ⟩ := eq_diff a;
    have : 1 = 1 —— 0 := rfl
    simp_rw [this, mul_eq, zero_mul, add_zero, one_mul]
  mul_one := by
    intro a; obtain ⟨ a1, a2, rfl ⟩ := eq_diff a;
    have : 1 = 1 —— 0 := rfl
    simp_rw [this, mul_eq, mul_zero, add_zero, mul_one, zero_add]

/-- 命题 4.1.6（代数定律）/ 习题 4.1.4 -/
instance Int.instCommRing : CommRing Int where
  left_distrib := by
    intro a b c
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
    obtain ⟨ c1, c2, rfl ⟩ := eq_diff c
    simp_rw [mul_eq, add_eq, mul_eq, mul_add, add_assoc, add_left_comm]
  right_distrib := by
    intro a b c
    obtain ⟨ a1, a2, rfl ⟩ := eq_diff a
    obtain ⟨ b1, b2, rfl ⟩ := eq_diff b
    obtain ⟨ c1, c2, rfl ⟩ := eq_diff c
    simp_rw [mul_eq, add_eq, mul_eq, add_mul, add_assoc, add_left_comm]
  zero_mul := by
    intro a; obtain ⟨ a1, a2, rfl ⟩ := eq_diff a;
    have : 0 = 0 —— 0 := rfl
    simp_rw [this, mul_eq, zero_mul, add_zero]
  mul_zero := by
    intro a; obtain ⟨ a1, a2, rfl ⟩ := eq_diff a;
    have : 0 = 0 —— 0 := rfl
    simp_rw [this, mul_eq, mul_zero, add_zero]

/-- 减法的定义 -/
theorem Int.sub_eq (a b:Int) : a - b = a + (-b) := by rfl

theorem Int.sub_eq_formal_sub (a b:ℕ) : (a:Int) - (b:Int) = a —— b := by
  rw [Int.natCast_eq, Int.natCast_eq, Int.sub_eq, Int.neg_eq, Int.add_eq, add_zero, zero_add]

/-- 命题 4.1.8（无零因子）/ 习题 4.1.5 -/
theorem Int.mul_eq_zero {a b:Int} (h: a * b = 0) : a = 0 ∨ b = 0 := by
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  have : 0 = 0 —— 0 := rfl
  simp_rw [mul_eq, this, eq, add_zero, zero_add] at h ⊢
  rcases Nat.le_total b1 b2 with (hle | hle)
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk] at h
    have h_eq : a1 * k = a2 * k := by
      nlinarith
    rcases eq_zero_or_pos k with (hkzero | hkpos)
    · right
      rw [hk, hkzero, add_zero]
    · left
      exact Nat.mul_right_cancel hkpos h_eq
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk] at h
    have h_eq : a1 * k = a2 * k := by
      nlinarith
    rcases eq_zero_or_pos k with (hkzero | hkpos)
    · right
      rw [hk, hkzero, add_zero]
    · left
      exact Nat.mul_right_cancel hkpos h_eq

/-- 推论 4.1.9（消去律）/ 习题 4.1.6 -/
theorem Int.mul_right_cancel₀ (a b c:Int) (h: a*c = b*c) (hc: c ≠ 0) : a = b := by
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  obtain ⟨c1, c2, rfl⟩ := eq_diff c
  have h1 : 0 = 0 —— 0 := rfl
  have h2 := not_iff_not.mpr (eq c1 c2 0 0)
  simp_rw [h1, h2, add_zero, zero_add, mul_eq, eq] at h hc ⊢
  rcases Nat.le_total c1 c2 with (hle | hle)
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    have hk_pos : 0 < k := by
      by_contra! H
      have hk_zero : k = 0 := by omega
      apply hc
      rw [hk, hk_zero, add_zero]
    rw [hk] at h
    have h_canceled : a2 * k + b1 * k = a1 * k + b2 * k := by
      have h_sorted : (a1 * c1 + a2 * c1 + b1 * c1 + b2 * c1) + (a2 * k + b1 * k) =
          (a1 * c1 + a2 * c1 + b1 * c1 + b2 * c1) + (a1 * k + b2 * k) := by
        calc
          (a1 * c1 + a2 * c1 + b1 * c1 + b2 * c1) + (a2 * k + b1 * k)
              = a1 * c1 + a2 * (c1 + k) + b1 * (c1 + k) + b2 * c1 := by ring
          _ = b1 * c1 + b2 * (c1 + k) + a1 * (c1 + k) + a2 * c1 := by
            simpa [add_assoc] using h
          _ = (a1 * c1 + a2 * c1 + b1 * c1 + b2 * c1) + (a1 * k + b2 * k) := by ring
      exact Nat.add_left_cancel h_sorted
    have h_mul : (a2 + b1) * k = (a1 + b2) * k := by
      calc
        (a2 + b1) * k = a2 * k + b1 * k := by ring
        _ = a1 * k + b2 * k := h_canceled
        _ = (a1 + b2) * k := by ring
    have h_temp : a2 + b1 = a1 + b2 :=
      Nat.mul_right_cancel hk_pos h_mul
    omega
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    have hk_pos : 0 < k := by
      by_contra! H
      have hk_zero : k = 0 := by omega
      apply hc
      rw [hk, hk_zero, add_zero]
    rw [hk] at h
    have h_canceled : a1 * k + b2 * k = b1 * k + a2 * k := by
      have h_sorted : (a1 * c2 + a2 * c2 + b1 * c2 + b2 * c2) + (a1 * k + b2 * k) =
          (a1 * c2 + a2 * c2 + b1 * c2 + b2 * c2) + (b1 * k + a2 * k) := by
        calc
          (a1 * c2 + a2 * c2 + b1 * c2 + b2 * c2) + (a1 * k + b2 * k)
              = a1 * (c2 + k) + a2 * c2 + b1 * c2 + b2 * (c2 + k) := by ring
          _ = b1 * (c2 + k) + b2 * c2 + a1 * c2 + a2 * (c2 + k) := by
            simpa [add_assoc] using h
          _ = (a1 * c2 + a2 * c2 + b1 * c2 + b2 * c2) + (b1 * k + a2 * k) := by ring
      exact Nat.add_left_cancel h_sorted
    have h_mul : (a1 + b2) * k = (b1 + a2) * k := by
      calc
        (a1 + b2) * k = a1 * k + b2 * k := by ring
        _ = b1 * k + a2 * k := h_canceled
        _ = (b1 + a2) * k := by ring
    have h_temp : a1 + b2 = b1 + a2 :=
      Nat.mul_right_cancel hk_pos h_mul
    omega

/-- 定义 4.1.10（整数的序） -/
instance Int.instLE : LE Int where
  le n m := ∃ a:ℕ, m = n + a

/-- 定义 4.1.10（整数的序） -/
instance Int.instLT : LT Int where
  lt n m := n ≤ m ∧ n ≠ m

theorem Int.le_iff (a b:Int) : a ≤ b ↔ ∃ t:ℕ, b = a + t := by rfl

theorem Int.lt_iff (a b:Int): a < b ↔ (∃ t:ℕ, b = a + t) ∧ a ≠ b := by rfl

/-- 引理 4.1.11(a)（序的性质）/ 习题 4.1.7 -/
theorem Int.lt_iff_exists_positive_difference (a b:Int) : a < b ↔ ∃ n:ℕ, n ≠ 0 ∧ b = a + n := by
  rw [Int.lt_iff]
  constructor
  · rintro ⟨⟨k, hk⟩, h2⟩
    use k
    apply And.intro _ hk
    intro hk2
    simp_rw [hk2, Int.natCast_ofNat, add_zero, eq_comm] at hk
    exact h2 hk
  rintro ⟨n, ⟨hn1, hn2⟩⟩
  constructor
  · use n
  contrapose! hn1
  nth_rw 1 [← add_zero b] at hn2
  simp_rw [hn1, add_left_cancel_iff, ← Int.natCast_ofNat, Int.natCast_inj, eq_comm] at hn2
  exact hn2

/-- 引理 4.1.11(b)（加法保持序）/ 习题 4.1.7 -/
theorem Int.add_lt_add_right {a b:Int} (c:Int) (h: a < b) : a+c < b+c := by
  rw [lt_iff]
  have ⟨⟨n, h1⟩, h2⟩ := (lt_iff a b).mp h
  constructor
  · use n; rw [h1, add_assoc, add_comm _ c, add_assoc]
  contrapose! h2
  apply add_right_cancel h2

/-- 引理 4.1.11(c)（正数乘法保持序）/ 习题 4.1.7 -/
theorem Int.mul_lt_mul_of_pos_right {a b c:Int} (hab : a < b) (hc: 0 < c) : a*c < b*c := by
  rw [lt_iff]
  have ⟨⟨n, h1⟩,h2⟩ := (lt_iff a b).mp hab
  have ⟨⟨m, h3⟩, h4⟩ := (lt_iff 0 c).mp hc
  rw [zero_add] at h3
  constructor
  · use n * m; rw [h1, right_distrib, add_left_cancel_iff, h3]; simp
  contrapose! h2
  apply mul_right_cancel₀ _ _ _ h2
  contrapose! h4
  rw [h4]

/-- 引理 4.1.11(d)（取负反转序）/ 习题 4.1.7 -/
theorem Int.neg_gt_neg {a b:Int} (h: b < a) : -a < -b := by
  rw [lt_iff]
  have ⟨⟨n, h1⟩,h2⟩ := (lt_iff b a).mp h
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  constructor
  · use n
    have h' : (n —— n) = 0 := by
      have : (0 : Int) = (0 —— 0) := by rfl
      rw [this, eq, add_zero, zero_add]
    have : (n: Int) = (n —— 0) := by rfl
    rw [h1, neg_eq, this, add_eq, neg_eq, add_eq, add_zero, add_zero, <- add_eq, h', add_zero]
  contrapose! h2
  rw [neg_eq, neg_eq, eq] at h2
  rw [eq, add_comm, h2, add_comm]

/-- 引理 4.1.11(d)（取负反转序）/ 习题 4.1.7 -/
theorem Int.neg_ge_neg {a b:Int} (h: b ≤ a) : -a ≤ -b := by
  rw [le_iff]
  have ⟨n, h1⟩ := (le_iff b a).mp h
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  use n
  have h' : (n —— n) = 0 := by
    have : (0 : Int) = (0 —— 0) := by rfl
    rw [this, eq, add_zero, zero_add]
  have : (n: Int) = (n —— 0) := by rfl
  rw [h1, neg_eq, this, add_eq, neg_eq, add_eq, add_zero, add_zero, <- add_eq, h', add_zero]

/-- 引理 4.1.11(e)（序的传递性）/ 习题 4.1.7 -/
theorem Int.lt_trans {a b c:Int} (hab: a < b) (hbc: b < c) : a < c := by
  rw [lt_iff_exists_positive_difference]
  obtain ⟨n, hn1, hn2⟩ := (lt_iff_exists_positive_difference a b).mp hab
  obtain ⟨m, hm1, hm2⟩ := (lt_iff_exists_positive_difference b c).mp hbc
  use n + m
  constructor
  · contrapose! hn1; omega
  rw [hm2, hn2, add_assoc, add_left_cancel_iff]; simp

/-- 引理 4.1.11(f)（序的三歧性）/ 习题 4.1.7 -/
theorem Int.trichotomous' (a b:Int) : a > b ∨ a < b ∨ a = b := by
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  have h := Nat.lt_trichotomy (a1 + b2) (b1 + a2)
  rcases h with (h | h | h)
  · right; left
    rw [lt_iff]
    have hle : a1 + b2 ≤ b1 + a2 := Nat.le_of_lt h
    obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
    refine ⟨?_, ?_⟩
    · use t
      apply (eq _ _ _ _).mpr
      omega
    · apply mt (eq _ _ _ _).mp
      exact Nat.ne_of_lt h
  · right; right
    rw [eq, h]
  · left
    have hb_lt_a : b1 —— b2 < a1 —— a2 := by
      rw [lt_iff]
      have hle : b1 + a2 ≤ a1 + b2 := Nat.le_of_lt h
      obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
      refine ⟨?_, ?_⟩
      · use t
        apply (eq _ _ _ _).mpr
        omega
      · apply mt (eq _ _ _ _).mp
        exact Nat.ne_of_lt h
    exact hb_lt_a

/-- 引理 4.1.11(f)（序的三歧性）/ 习题 4.1.7 -/
theorem Int.not_gt_and_lt (a b:Int) : ¬ (a > b ∧ a < b) := by
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  rintro ⟨hgt, hlt⟩
  rcases (lt_iff _ _).mp hgt with ⟨⟨t, ht⟩, hne⟩
  rcases (lt_iff _ _).mp hlt with ⟨⟨s, hs⟩, hne'⟩
  have hne_nat : b1 + a2 ≠ a1 + b2 := by
    intro h; apply hne; rw [eq, h]
  have hne'_nat : a1 + b2 ≠ b1 + a2 := by
    intro h; apply hne'; rw [eq, h]
  have hsum1 : a1 + b2 = b1 + a2 + t := by
    simpa [Int.natCast_eq, add_eq, eq, add_assoc, add_comm, add_left_comm] using ht
  have hsum2 : b1 + a2 = a1 + b2 + s := by
    simpa [Int.natCast_eq, add_eq, eq, add_assoc, add_comm, add_left_comm] using hs
  have hgt' : b1 + a2 < a1 + b2 :=
    Nat.lt_of_le_of_ne (by omega) hne_nat
  have hlt' : a1 + b2 < b1 + a2 :=
    Nat.lt_of_le_of_ne (by omega) hne'_nat
  exact Nat.lt_asymm hgt' hlt'

/-- 引理 4.1.11(f)（序的三歧性）/ 习题 4.1.7 -/
theorem Int.not_gt_and_eq (a b:Int) : ¬ (a > b ∧ a = b) := by
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  rintro ⟨hgt, heq⟩
  rw [eq] at heq
  rcases (lt_iff _ _).mp hgt with ⟨⟨t, ht⟩, hne⟩
  have hne_nat : b1 + a2 ≠ a1 + b2 := by
    intro h; apply hne; rw [eq, h]
  apply hne_nat
  rw [heq]

/-- 引理 4.1.11(f)（序的三歧性）/ 习题 4.1.7 -/
theorem Int.not_lt_and_eq (a b:Int) : ¬ (a < b ∧ a = b) := by
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  obtain ⟨b1, b2, rfl⟩ := eq_diff b
  rintro ⟨hlt, heq⟩
  rw [eq] at heq
  rcases (lt_iff _ _).mp hlt with ⟨⟨t, ht⟩, hne⟩
  have hne_nat : a1 + b2 ≠ b1 + a2 := by
    intro h; apply hne; rw [eq, h]
  apply hne_nat
  rw [heq]

/--（不在教科书中）建立序的可判定性 -/
instance Int.decidableRel : DecidableRel (· ≤ · : Int → Int → Prop) := by
  intro n m
  have : ∀ (n:PreInt) (m: PreInt),
      Decidable (Quotient.mk PreInt.instSetoid n ≤ Quotient.mk PreInt.instSetoid m) := by
    intro ⟨ a,b ⟩ ⟨ c,d ⟩
    change Decidable (a —— b ≤ c —— d)
    cases (a + d).decLe (c + b) with
      | isTrue h =>
        apply isTrue
        rw [le_iff]
        have hle : a + d ≤ c + b := h
        obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hle
        use t
        apply (eq _ _ _ _).mpr
        omega
      | isFalse h =>
        apply isFalse
        rw [le_iff]
        intro hle
        rcases hle with ⟨t, ht⟩
        apply h
        have hsum : c + b = a + d + t := by
          simpa [Int.natCast_eq, add_eq, eq, add_assoc, add_comm, add_left_comm] using ht
        omega
  exact Quotient.recOnSubsingleton₂ n m this

/--（不在教科书中）0 是唯一的加法单位元 -/
lemma Int.is_additive_identity_iff_eq_0 (b : Int) : (∀ a, a = a + b) ↔ b = 0 := by
  constructor
  · intro h
    have h0 : (0 : Int) = (0 : Int) + b := h 0
    simpa [zero_add, eq_comm] using h0
  · intro h
    subst b
    intro a
    simp [add_zero]

/-- 辅助引理：antisymm，避免 LinearOrder 实例中的循环依赖 -/
theorem Int.le_antisymm' (a b : Int) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  rw [le_iff] at h1 h2
  rcases h1 with ⟨t, ht⟩
  rcases h2 with ⟨s, hs⟩
  have ht_nonneg : 0 ≤ (t : Int) := by
    rw [le_iff]
    use t
    simp
  have hs_nonneg : 0 ≤ (s : Int) := by
    rw [le_iff]
    use s
    simp
  have htemp : a + ((t : Int) + (s : Int)) = a := by
    calc
      a + ((t : Int) + (s : Int)) = (a + (t : Int)) + (s : Int) := by ring
      _ = b + (s : Int) := by rw [ht]
      _ = a := hs.symm
  have hsum_int : (t : Int) + (s : Int) = 0 :=
    add_left_cancel (a := a) <| calc
      a + ((t : Int) + (s : Int)) = a := htemp
      _ = a + 0 := by simp
  have hsum_nat : t + s = 0 := by
    apply (Int.natCast_inj (t + s) 0).mp
    calc
      ((t + s : ℕ) : Int) = (t : Int) + (s : Int) := by simp
      _ = 0 := hsum_int
  have ht0 : t = 0 := by omega
  have hs0 : s = 0 := by omega
  calc
    a = b + (s : Int) := hs
    _ = b := by simp [hs0]

/--（不在教科书中）Int 具有线性序结构 -/
instance Int.instLinearOrder : LinearOrder Int where
  le_refl := by
    intro a
    rw [le_iff]
    use 0
    simp
  le_trans := by
    intro a b c h1 h2
    rw [le_iff] at h1 h2 ⊢
    rcases h1 with ⟨t, ht⟩
    rcases h2 with ⟨s, hs⟩
    use t + s
    calc
      c = b + (s : Int) := hs
      _ = (a + (t : Int)) + (s : Int) := by rw [ht]
      _ = a + ((t : Int) + (s : Int)) := by ring
      _ = a + ((t + s : ℕ) : Int) := by simp
  lt_iff_le_not_ge := by
    intro a b
    constructor
    · intro ⟨hle, hne⟩
      refine ⟨hle, ?_⟩
      intro hge
      apply hne
      exact le_antisymm' a b hle hge
    · intro ⟨hle, hng⟩
      refine ⟨hle, ?_⟩
      intro h_eq
      apply hng
      simpa [h_eq] using hle
  le_antisymm := le_antisymm'
  le_total := by
    intro a b
    rcases trichotomous' a b with (h | h | h)
    · right; exact h.1
    · left; exact h.1
    · left; rw [h]; rw [le_iff]; use 0; simp
  toDecidableLE := decidableRel

/-- 习题 4.1.3 -/
theorem Int.neg_one_mul (a:Int) : -1 * a = -a := by
  have : -1 = 0 —— 1 := by rfl
  obtain ⟨a1, a2, rfl⟩ := eq_diff a
  simp_rw [this, mul_eq, neg_eq, zero_mul, zero_add, one_mul]

/-- 习题 4.1.8 -/
theorem Int.no_induction : ∃ P: Int → Prop, (P 0 ∧ ∀ n, P n → P (n+1)) ∧ ¬ ∀ n, P n := by
  refine ⟨λ n => 0 ≤ n, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · show 0 ≤ (0 : Int); rw [le_iff]; use 0; simp
    · intro n hn
      have hn' : 0 ≤ n := hn
      rw [le_iff] at hn' ⊢
      rcases hn' with ⟨t, ht⟩
      use t + 1
      calc
        n + 1 = (0 + (t : Int)) + 1 := by rw [ht]
        _ = (t : Int) + 1 := by simp
        _ = 0 + ((t + 1 : ℕ) : Int) := by simp
  · intro h
    have hneg : ¬ 0 ≤ (-1 : Int) := by
      rw [le_iff]
      intro h'
      rcases h' with ⟨t, ht⟩
      have h_eq_preint : (0——1 : Int) = (t——0 : Int) := by
        calc
          (0——1 : Int) = (-1 : Int) := rfl
          _ = (t : Int) := by
            simpa using ht
          _ = (t——0 : Int) := rfl
      have hzero : 0 = t + 1 := by
        simpa using (eq 0 1 t 0).mp h_eq_preint
      exact (Nat.succ_ne_zero t) hzero.symm
    exact hneg (h (-1))

/-- 非负数平方为非负。这对证明一般情况有用 -/
lemma Int.sq_nonneg_of_pos (n:Int) (h: 0 ≤ n) : 0 ≤ n*n := by
  rw [le_iff] at h
  rcases h with ⟨t, ht⟩
  have hn : n = (t : Int) := by simpa using ht
  rw [hn]
  rw [le_iff]
  use t * t
  simp [Int.natCast_eq, mul_eq]

/-- 习题 4.1.9。任何整数的平方都是非负的 -/
theorem Int.sq_nonneg (n:Int) : 0 ≤ n*n := by
  rcases trichotomous' n 0 with (h | h | h)
  · exact sq_nonneg_of_pos n h.1
  · have hpos : 0 ≤ -n := by
      have : n ≤ 0 := h.1
      have := Int.neg_ge_neg this
      simpa using this
    have h_sq : (-n)*(-n) = n*n := by ring
    rw [← h_sq]
    exact sq_nonneg_of_pos (-n) hpos
  · rw [h]
    rw [le_iff]
    use 0
    simp

/-- 习题 4.1.9 -/
theorem Int.sq_nonneg' (n:Int) : ∃ (m:Nat), n*n = m := by
  have h0 : 0 ≤ n*n := sq_nonneg n
  rw [le_iff] at h0
  rcases h0 with ⟨m, hm⟩
  use m
  simpa using hm

/--
  不在教科书中：创建 {name}`Int` 与 {lean}`ℤ` 之间的等价。
  这需要熟悉 Mathlib 版本整数的 API。
-/
abbrev Int.equivInt : Int ≃ ℤ where
  toFun := Quotient.lift (fun ⟨ a, b ⟩ ↦ (a : ℤ) - (b : ℤ)) (by
    intro a b h
    have h' : (a.1 : ℤ) - (a.2 : ℤ) = (b.1 : ℤ) - (b.2 : ℤ) := by
      have hz : (a.1 : ℤ) + (b.2 : ℤ) = (b.1 : ℤ) + (a.2 : ℤ) := by exact_mod_cast h
      omega
    simpa)
  invFun := λ z =>
    if hz : 0 ≤ z then
      (z.natAbs : ℕ) —— (0 : ℕ)
    else
      (0 : ℕ) —— (z.natAbs : ℕ)
  left_inv n := by
    obtain ⟨a, b, rfl⟩ := eq_diff n
    dsimp
    set z := (a : ℤ) - (b : ℤ) with hz
    by_cases hzpos : 0 ≤ z
    · have hazb : (b : ℕ) ≤ a := by
        omega
      have h_natAbs_eq : (z.natAbs : ℕ) = a - b := by
        apply (Nat.cast_inj (R := ℤ)).mp
        calc
          ((z.natAbs : ℕ) : ℤ) = z := Int.natAbs_of_nonneg hzpos
          _ = (a : ℤ) - (b : ℤ) := rfl
          _ = ((a - b : ℕ) : ℤ) := by
            rw [Nat.cast_sub hazb]
      simp [hzpos, h_natAbs_eq]
      apply (eq (a - b) 0 a b).mpr
      omega
    · have hzneg : z ≤ 0 := by omega
      have hbza : (a : ℕ) ≤ b := by
        omega
      have h_natAbs_eq : (z.natAbs : ℕ) = b - a := by
        apply (Nat.cast_inj (R := ℤ)).mp
        calc
          ((z.natAbs : ℕ) : ℤ) = -z := by
            calc
              ((z.natAbs : ℕ) : ℤ) = ((-z).natAbs : ℤ) := by simp
              _ = -z := Int.natAbs_of_nonneg (by omega)
          _ = -((a : ℤ) - (b : ℤ)) := rfl
          _ = (b : ℤ) - (a : ℤ) := by ring
          _ = ((b - a : ℕ) : ℤ) := by
            rw [Nat.cast_sub hbza]
      simp [hzpos, h_natAbs_eq]
      apply (eq 0 (b - a) a b).mpr
      omega
  right_inv n := by
    dsimp
    by_cases hnpos : 0 ≤ n
    · have h_natAbs : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hnpos
      simp [hnpos, h_natAbs]
    · have hnneg : n ≤ 0 := by omega
      have h_natAbs : (n.natAbs : ℤ) = -n := by
        calc
          (n.natAbs : ℤ) = ((-n).natAbs : ℤ) := by simp
          _ = -n := Int.natAbs_of_nonneg (by omega)
      simp [hnpos, h_natAbs]

/-- 不在教科书中：等价保持序和环运算 -/
abbrev Int.equivInt_ordered_ring : Int ≃+*o ℤ where
  toEquiv := equivInt
  map_add' := by
    intro x y
    obtain ⟨a1, a2, rfl⟩ := eq_diff x
    obtain ⟨b1, b2, rfl⟩ := eq_diff y
    dsimp
    simp [add_eq]
    ring
  map_mul' := by
    intro x y
    obtain ⟨a1, a2, rfl⟩ := eq_diff x
    obtain ⟨b1, b2, rfl⟩ := eq_diff y
    dsimp
    simp [mul_eq]
    ring
  map_le_map_iff' := by
    intro x y
    obtain ⟨a1, a2, rfl⟩ := eq_diff x
    obtain ⟨b1, b2, rfl⟩ := eq_diff y
    dsimp
    have hR : (a1 —— a2 ≤ b1 —— b2) ↔ ∃ t : ℕ, b1 + a2 = (a1 + t) + b2 := by
      rw [le_iff]
      constructor
      · rintro ⟨t, ht⟩
        use t
        have h_expand : (a1——a2) + (t : Int) = (a1 + t) —— a2 := by
          simp [Int.natCast_eq, add_eq]
        rw [h_expand] at ht
        exact ((eq (a1 + t) a2 b1 b2).mp ht.symm).symm
      · rintro ⟨t, ht⟩
        use t
        calc
          (b1——b2 : Int) = (a1 + t) —— a2 := by
            apply (eq _ _ _ _).mpr
            omega
          _ = (a1 + t) —— (a2 + 0) := by simp
          _ = (a1——a2) + (t——0) := by rw [← add_eq]
          _ = (a1——a2) + (t : Int) := by rw [Int.natCast_eq]
    have hL : ((a1 : ℤ) - (a2 : ℤ) ≤ (b1 : ℤ) - (b2 : ℤ)) ↔ ∃ t : ℕ, b1 + a2 = (a1 + t) + b2 := by
      constructor
      · intro h
        have hz : (a1 : ℤ) + (b2 : ℤ) ≤ (b1 : ℤ) + (a2 : ℤ) := by omega
        have hn : (a1 + b2 : ℕ) ≤ (b1 + a2 : ℕ) := by exact_mod_cast hz
        obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le hn
        use t
        omega
      · rintro ⟨t, ht⟩
        omega
    simp [hL, hR]

end Section_4_1
