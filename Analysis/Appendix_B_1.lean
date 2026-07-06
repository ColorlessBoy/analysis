import Mathlib.Tactic

/-!
# Analysis I, Appendix B.1: The decimal representation of natural numbers

Am implementation of the decimal representation of Mathlib's natural numbers {lean}`ℕ`.

This is separate from the way decimal numerals are already represenated in Mathlib via the {name}`OfNat` typeclass.
-/

namespace AppendixB

/- The ten digits, together with the base 10 -/
example : 0 = Nat.zero := rfl
example : 1 = (0:Nat).succ := rfl
example : 2 = (1:Nat).succ := rfl
example : 3 = (2:Nat).succ := rfl
example : 4 = (3:Nat).succ := rfl
example : 5 = (4:Nat).succ := rfl
example : 6 = (5:Nat).succ := rfl
example : 7 = (6:Nat).succ := rfl
example : 8 = (7:Nat).succ := rfl
example : 9 = (8:Nat).succ := rfl
example : 10 = (9:Nat).succ := rfl

/-- Definition B.1.1 -/
def Digit := Fin 10

instance Digit.instZero : Zero Digit := ⟨0, by decide⟩
instance Digit.instOne : One Digit := ⟨1, by decide⟩
instance Digit.instTwo : OfNat Digit 2 := ⟨2, by decide⟩
instance Digit.instThree : OfNat Digit 3 := ⟨3, by decide⟩
instance Digit.instFour : OfNat Digit 4 := ⟨4, by decide⟩
instance Digit.instFive : OfNat Digit 5 := ⟨5, by decide⟩
instance Digit.instSix : OfNat Digit 6 := ⟨6, by decide⟩
instance Digit.instSeven : OfNat Digit 7 := ⟨7, by decide⟩
instance Digit.instEight : OfNat Digit 8 := ⟨8, by decide⟩
instance Digit.instNine : OfNat Digit 9 := ⟨9, by decide⟩

instance Digit.instFintype : Fintype Digit := Fin.fintype 10
instance Digit.instDecidableEq : DecidableEq Digit := instDecidableEqFin 10

instance Digit.instInhabited : Inhabited Digit := ⟨ 0 ⟩

@[coe]
abbrev Digit.toNat (d:Digit) : ℕ := d.val

instance Digit.instCoeNat : Coe Digit Nat where
  coe := toNat

theorem Digit.lt (d:Digit) : (d:ℕ) < 10 := d.isLt

abbrev Digit.mk {n:ℕ} (h: n < 10) : Digit := ⟨n, h⟩

@[simp]
theorem Digit.toNat_mk {n:ℕ} (h: n < 10) : (Digit.mk h:ℕ) = n := rfl

@[simp]
theorem Digit.inj (d d':Digit) : d = d' ↔ (d:ℕ) = d' := by grind

theorem Digit.mk_eq_iff (d:Digit) {n:ℕ} (h: n < 10) : d = mk h ↔ (d:ℕ) = n := by
  convert Digit.inj d (mk h)
#check (0:Digit)
#check (1:Digit)
#check (2:Digit)
#check (3:Digit)
#check (4:Digit)
#check (5:Digit)
#check (6:Digit)
#check (7:Digit)
#check (8:Digit)
#check (9:Digit)

theorem Digit.eq (n: Digit) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by
  fin_cases n <;> simp +decide

/-- Definition B.1.2 -/
structure PosintDecimal where
  digits : List Digit
  nonempty : digits ≠ []
  nonzero : digits.head nonempty ≠ 0

theorem PosintDecimal.congr' {p q:PosintDecimal} (h: p.digits = q.digits) : p = q := by
  obtain ⟨ pd, _, _ ⟩ := p
  obtain ⟨ qd, _, _ ⟩ := q
  congr

theorem PosintDecimal.congr {p q:PosintDecimal} (h: p.digits.length = q.digits.length)
  (h': ∀ (n:ℕ) (h₁ : n < p.digits.length) (h₂: n < q.digits.length), p.digits.get ⟨ n, h₁ ⟩ = q.digits.get ⟨ n, h₂ ⟩) : p = q := by
  apply congr'
  simp_all [List.ext_get_iff]

abbrev PosintDecimal.head (p:PosintDecimal): Digit := p.digits.head p.nonempty

theorem PosintDecimal.head_ne_zero (p:PosintDecimal) : p.head ≠ 0 := p.nonzero

theorem PosintDecimal.head_ne_zero' (p:PosintDecimal) : (p.head:ℕ) ≠ 0 := by
  by_contra!
  apply head_ne_zero p
  simp_all [Digit.toNat, Digit.inj]; rfl

theorem PosintDecimal.length_pos (p:PosintDecimal) : 0 < p.digits.length := by
  simp [List.length_pos_iff, p.nonempty]

/-- A slightly clunky way of creating decimals. -/
def PosintDecimal.mk' (head:Digit) (tail:List Digit) (h: head ≠ 0) : PosintDecimal := {
  digits := head :: tail
  nonempty := by aesop
  nonzero := h
}

-- the positive integer decimal 314
#check PosintDecimal.mk' 3 [1, 4] (by decide)

-- the positive integer decimal 3
#check PosintDecimal.mk' 3 [] (by decide)

-- the positive integer decimal 10
#check PosintDecimal.mk' 1 [0] (by decide)

/-- We are indexing digits in a decimal from left to right rather than from right to left, thus necessitating a reversal here. -/
@[coe]
def PosintDecimal.toNat (p:PosintDecimal) : Nat :=
  ∑ i:Fin p.digits.length, p.digits[p.digits.length - 1 - ↑i].toNat * 10 ^ (i:ℕ)

instance PosintDecimal.instCoeNat : Coe PosintDecimal Nat where
  coe := toNat

example : (PosintDecimal.mk' 3 [1, 4] (by decide):ℕ) = 314 := by decide

/-- Remark B.1.3 -/
@[simp]
theorem PosintDecimal.ten_eq_ten : (mk' 1 [0] (by decide):ℕ) = 10 := by
  decide

theorem PosintDecimal.digit_eq {d:Digit} (h: d ≠ 0) : (mk' d [] h:ℕ) = d := by
  simp [toNat, mk']

theorem PosintDecimal.pos (p:PosintDecimal) : 0 < (p:ℕ) := by
  simp [toNat]
  calc
    _ < (p.head:ℕ) * 10 ^ (p.digits.length - 1) := by
      have := p.head_ne_zero'
      positivity
    _ ≤ _ := by
      have := p.length_pos
      set a : Fin p.digits.length := ⟨ p.digits.length - 1, by omega ⟩
      convert Finset.single_le_sum _ (Finset.mem_univ a)
      . simp [a, head, List.head_eq_getElem]
      . infer_instance
      grind

/-- An operation implicit in the proof of Theorem B.1.4: -/
abbrev PosintDecimal.append (p:PosintDecimal) (d:Digit) : PosintDecimal :=
  mk' p.head (p.digits.tail ++ [d]) p.head_ne_zero

/-- {name}`toNat` equals Horner (left-fold) evaluation of the digit list. -/
theorem PosintDecimal.toNat_eq_foldl (q : PosintDecimal) :
    q.toNat = q.digits.foldl (fun acc (d : Digit) => acc * 10 + d.toNat) 0 := by
  suffices h : ∀ (L : List Digit) (acc : ℕ),
      L.foldl (fun a (d : Digit) => a * 10 + d.toNat) acc =
      acc * 10 ^ L.length + ∑ i : Fin L.length, (L[L.length - 1 - ↑i]).toNat * 10 ^ (↑i : ℕ)
    from by simp [toNat, h q.digits 0]
  intro L; induction L with
  | nil => simp
  | cons a t ih =>
    intro acc; simp only [List.foldl_cons, List.length_cons]
    -- Decompose the Fin (t.length+1) sum: last term is a*10^|t|, rest matches the Fin t.length sum
    have : ∑ x : Fin (t.length + 1), ((a :: t)[t.length - ↑x] : ℕ) * 10 ^ (↑x : ℕ) =
        (∑ x : Fin t.length, (t[t.length - 1 - ↑x] : ℕ) * 10 ^ (↑x : ℕ)) + a * 10 ^ t.length := by
      refine (Fin.sum_univ_castSucc _).trans ?_
      congr 1 <;> grind
    grind

@[simp]
theorem PosintDecimal.append_toNat (p:PosintDecimal) (d:Digit) :
  (p.append d:ℕ) = d.toNat + 10 * p.toNat  := by
  rw [toNat_eq_foldl, toNat_eq_foldl]; simp only [append, mk']
  rw [show p.head :: (p.digits.tail ++ [d]) = p.digits ++ [d] from by
    simp [head, ← List.cons_append, List.cons_head_tail]]
  rw [List.foldl_append]; simp [List.foldl]; ring

theorem PosintDecimal.eq_append {p:PosintDecimal} (h: 2 ≤ p.digits.length) : ∃ (q:PosintDecimal) (d:Digit), p = q.append d := by
  use mk' p.head (p.digits.tail.dropLast) p.head_ne_zero
  set a := p.digits.getLast p.nonempty; use a
  apply congr'
  simp [mk']
  rw [←p.digits.cons_head_tail p.nonempty]
  congr 1
  convert (List.dropLast_append_getLast _).symm using 2; grind
  simp [←List.length_pos_iff]; omega

/-- Theorem B.1.4 (Uniqueness and existence of decimal representations) -/
theorem PosintDecimal.exists_unique (n:ℕ) : n > 0 → ∃! p:PosintDecimal, (p:ℕ) = n := by
  -- this proof is written to follow the structure of the original text.
  apply n.case_strong_induction_on
  . simp
  -- note: the variable `m` in the text is referred to as `m+1` here.
  clear n; intro m hind _
  obtain hm | hm := lt_or_ge m 9
  . apply ExistsUnique.intro (mk' (.mk (show m+1 < 10 by omega)) [] (by simp [Digit.mk]))
    . simp [mk', Digit.mk, toNat, Digit.toNat]
    intro d hd
    obtain hdl | hdl := lt_or_ge d.digits.length 2
    . replace hdl : d.digits.length = 1 := by linarith [d.length_pos]
      have _subsing : Subsingleton (Fin d.digits.length) := by simp [Fin.subsingleton_iff_le_one, hdl]
      let zero : Fin d.digits.length := ⟨ 0, by omega ⟩
      simp [toNat, hdl, Fintype.sum_subsingleton _ zero, zero, Digit.toNat] at hd
      apply congr
      . simp [hdl, mk']
      intro i hi₁ hi₂
      replace hi₁ : i = 0 := by omega
      simp [hi₁, mk', Digit.mk, hd]
    have : d.toNat ≥ 10 := calc
      _ ≥ (d.head:ℕ) * 10^(d.digits.length-1) := by
        set a : Fin d.digits.length := ⟨ d.digits.length - 1, by omega ⟩
        convert Finset.single_le_sum _ (Finset.mem_univ a)
        . simp [a, head, List.head_eq_getElem]
        . infer_instance
        intros; positivity
      _ ≥ 1 * 10^(2-1) := by
        gcongr
        . have := d.head_ne_zero'; omega
        norm_num
      _ = 10 := by norm_num
    linarith
  have := (m+1).mod_add_div 10
  set s := (m+1)/10
  set r := (m+1) % 10
  have hr : r < 10 := by grind
  specialize hind s _ _ <;> try linarith
  choose b hb huniq using hind; simp at huniq
  apply ExistsUnique.intro (b.append (.mk hr))
  . simp [←this, hb]
  intro a ha
  obtain hal | hal := lt_or_ge a.digits.length 2
  . replace hal : a.digits.length = 1 := by linarith [a.length_pos]
    have _subsing : Subsingleton (Fin a.digits.length) := by simp [Fin.subsingleton_iff_le_one, hal]
    let zero : Fin a.digits.length := ⟨ 0, by linarith ⟩
    simp [toNat, hal, Fintype.sum_subsingleton _ zero, zero, Digit.toNat] at ha
    observe : a.digits[0].val < 10
    linarith
  obtain ⟨ b', b'₀, rfl ⟩ := eq_append hal
  simp [←this] at ha
  observe : (b'₀:ℕ) < 10
  replace : (s:ℤ) = (b':ℕ) := by omega
  have hb'₀r: (b'₀:ℕ) = (r:ℤ) := by omega
  simp at *
  rw [←b'₀.mk_eq_iff hr] at hb'₀r
  rw [huniq b' this.symm, hb'₀r]

@[simp]
theorem PosintDecimal.coe_inj (p q:PosintDecimal) : (p:ℕ) = (q:ℕ) ↔ p = q := by
  constructor <;> intro h
  . exact (exists_unique _ q.pos).unique h rfl
  rw [h]


inductive IntDecimal where
  | zero : IntDecimal
  | pos : PosintDecimal → IntDecimal
  | neg : PosintDecimal → IntDecimal

def IntDecimal.toInt : IntDecimal → Int
  | zero => 0
  | pos p => p.toNat
  | neg p => -p.toNat

instance IntDecimal.instCoeInt : Coe IntDecimal Int where
  coe := toInt

example : (IntDecimal.neg (PosintDecimal.mk' 3 [1, 4] (by decide)):ℤ) = -314 := by decide

theorem IntDecimal.Int_bij : Function.Bijective IntDecimal.toInt := by
  constructor
  . intro p q hpq
    cases p with
    | zero => cases q with
      | zero => rfl
      | pos q => simp [toInt] at hpq; linarith [q.pos]
      | neg q => simp [toInt] at hpq; linarith [q.pos]
    | pos p => cases q with
      | zero => simp [toInt] at hpq; linarith [p.pos]
      | pos q => simpa [toInt] using hpq
      | neg q => simp [toInt] at hpq; linarith [q.pos]
    | neg p => cases q with
      | zero => simp [toInt] at hpq; linarith [p.pos]
      | pos q => simp [toInt] at hpq; linarith [q.pos]
      | neg q => simpa [toInt] using hpq
  intro n
  obtain h | rfl | h := lt_trichotomy n 0
  . generalize e: -n = m
    lift m to Nat using (by omega)
    choose p hp _ using PosintDecimal.exists_unique _ (show 0 < m by omega)
    use neg p
    simp [toInt, hp, ←e]
  . use zero; simp [toInt]
  lift n to Nat using (by omega); simp at h
  choose p hp _ using PosintDecimal.exists_unique _ h
  use pos p
  simp [toInt, hp]

abbrev PosintDecimal.digit (p:PosintDecimal) (i:ℕ) : Digit :=
  if h: i < p.digits.length then p.digits[p.digits.length - i - 1] else 0

abbrev PosintDecimal.carry (p q:PosintDecimal) : ℕ → ℕ := Nat.rec 0 (fun i ε ↦ if ((p.digit i:ℕ) + (q.digit i:ℕ) + ε) < 10 then 0 else 1)

theorem PosintDecimal.carry_zero (p q:PosintDecimal) : p.carry q 0 = 0 := by convert Nat.rec_zero _ _

theorem PosintDecimal.carry_succ (p q:PosintDecimal) (i:ℕ) : p.carry q (i+1) = if ((p.digit i:ℕ) + (q.digit i:ℕ) + p.carry q i < 10) then 0 else 1 :=
  Nat.rec_add_one 0 (fun i ε ↦ if ((p.digit i:ℕ) + (q.digit i:ℕ) + ε) < 10 then 0 else 1) i

abbrev PosintDecimal.sum_digit (p q:PosintDecimal) (i:ℕ) : ℕ :=
  if (p.digit i + q.digit i + (p.carry q) i < 10) then
    p.digit i + q.digit i + (p.carry q) i
  else
    p.digit i + q.digit i + (p.carry q) i - 10

theorem PosintDecimal.carry_le_one (p q:PosintDecimal) (i:ℕ) : p.carry q i ≤ 1 := by
  induction i with
  | zero =>
    rw [carry_zero]
    omega
  | succ i ih =>
    rw [carry_succ]
    split <;> omega

/-- Exercise B.1.1 -/
theorem PosintDecimal.sum_digit_lt (p q:PosintDecimal) (i:ℕ) :
  p.sum_digit q i < 10 := by
  dsimp [sum_digit]
  have h1 : (p.digit i : ℕ) < 10 := Digit.lt _
  have h2 : (q.digit i : ℕ) < 10 := Digit.lt _
  have h3 : p.carry q i ≤ 1 := carry_le_one _ _ _
  split <;> omega

/-- Define this number such that it satisfies the two following theorems. -/
def PosintDecimal.sum_digit_top (p q:PosintDecimal) : ℕ :=
  let N := max p.digits.length q.digits.length
  if p.carry q N = 1 then N else N - 1

theorem PosintDecimal.leading_nonzero (p q:PosintDecimal) :
    p.sum_digit q (p.sum_digit_top q) ≠ 0 := by
  unfold sum_digit_top
  dsimp
  set N := max p.digits.length q.digits.length with hN
  have hNpos : 0 < N := by
    rw [hN]
    exact lt_of_lt_of_le p.length_pos (le_max_left _ _)
  have hcarry_le_one : p.carry q N ≤ 1 := carry_le_one _ _ _
  split
  · rename_i hcarry
    -- case: p.carry q N = 1, so sum_digit_top = N
    have hp_digit_N : p.digit N = (0 : Digit) := by
      dsimp [digit]
      have hNge : N ≥ p.digits.length := by
        rw [hN]; exact le_max_left _ _
      have : ¬ N < p.digits.length := by omega
      simp [this]
    have hq_digit_N : q.digit N = (0 : Digit) := by
      dsimp [digit]
      have hNge : N ≥ q.digits.length := by
        rw [hN]; exact le_max_right _ _
      have : ¬ N < q.digits.length := by omega
      simp [this]
    have hsum : p.sum_digit q N = 1 := by
      unfold sum_digit
      have hsum1 : (p.digit N : ℕ) + (q.digit N : ℕ) + (p.carry q) N = 1 := by
        simp [hp_digit_N, hq_digit_N, hcarry]
      have hlt : (p.digit N : ℕ) + (q.digit N : ℕ) + (p.carry q) N < 10 := by
        rw [hsum1]; norm_num
      rw [if_pos hlt, hsum1]
    simp [hsum]
  · rename_i hcarry
    -- case: p.carry q N ≠ 1, so sum_digit_top = N - 1
    have hcarry0 : p.carry q N = 0 := by
      have : p.carry q N ≤ 1 := hcarry_le_one
      omega
    have hsum_lt10 : (p.digit (N-1) : ℕ) + (q.digit (N-1) : ℕ) + p.carry q (N-1) < 10 := by
      have hsucc : N = (N-1) + 1 := by omega
      rw [hsucc, carry_succ] at hcarry0
      by_cases hlt : (p.digit (N-1) : ℕ) + (q.digit (N-1) : ℕ) + p.carry q (N-1) < 10
      · exact hlt
      · rw [if_neg hlt] at hcarry0
        omega
    have hsum_eq : p.sum_digit q (N-1) = (p.digit (N-1) : ℕ) + (q.digit (N-1) : ℕ) + p.carry q (N-1) := by
      unfold sum_digit
      split_ifs <;> simp
    rw [hsum_eq]
    have hnonzero : (p.digit (N-1) : ℕ) + (q.digit (N-1) : ℕ) + p.carry q (N-1) ≠ 0 := by
      have hN_cases : p.digits.length = N ∨ q.digits.length = N := by
        have hle_total : q.digits.length ≤ p.digits.length ∨ p.digits.length ≤ q.digits.length := le_total _ _
        rcases hle_total with (h | h)
        · left; rw [hN]; exact (Nat.max_eq_left h).symm
        · right; rw [hN]; exact (Nat.max_eq_right h).symm
      rcases hN_cases with (hp_len | hq_len)
      · -- p.digits.length = N
        have hp_digit_pos : (p.digit (N-1) : ℕ) ≠ 0 := by
          dsimp [digit]
          have h_index_lt_len : N-1 < p.digits.length := by
            rw [hp_len]; omega
          rw [dif_pos h_index_lt_len]
          have : p.digits.length - (N-1) - 1 = 0 := by
            rw [hp_len]; omega
          have hhead : p.digits[0] = p.head := by
            dsimp [head]
            simpa using (List.head_eq_getElem p.nonempty).symm
          simpa [this, hhead] using p.head_ne_zero'
        intro hzero
        apply hp_digit_pos
        omega
      · -- q.digits.length = N
        have hq_digit_pos : (q.digit (N-1) : ℕ) ≠ 0 := by
          dsimp [digit]
          have h_index_lt_len : N-1 < q.digits.length := by
            rw [hq_len]; omega
          rw [dif_pos h_index_lt_len]
          have : q.digits.length - (N-1) - 1 = 0 := by
            rw [hq_len]; omega
          have hhead : q.digits[0] = q.head := by
            dsimp [head]
            simpa using (List.head_eq_getElem q.nonempty).symm
          simpa [this, hhead] using q.head_ne_zero'
        intro hzero
        apply hq_digit_pos
        omega
    exact hnonzero

theorem PosintDecimal.out_of_range_eq_zero (p q:PosintDecimal) :
    ∀ i > ↑(p.sum_digit_top q), p.sum_digit q i = 0 := by
  unfold sum_digit_top
  dsimp
  set N := max p.digits.length q.digits.length with hN
  have hp_len_le_N : p.digits.length ≤ N := by
    rw [hN]; exact le_max_left _ _
  have hq_len_le_N : q.digits.length ≤ N := by
    rw [hN]; exact le_max_right _ _
  have hdigit_ge_N (k : ℕ) (hk : k ≥ N) : p.digit k = (0 : Digit) ∧ q.digit k = (0 : Digit) := by
    constructor
    · dsimp [digit]
      have : ¬ k < p.digits.length := not_lt.mpr (le_trans hp_len_le_N hk)
      simp [this]
    · dsimp [digit]
      have : ¬ k < q.digits.length := not_lt.mpr (le_trans hq_len_le_N hk)
      simp [this]
  have digit_val_zero (k : ℕ) (hk : k ≥ N) : (p.digit k : ℕ) = 0 ∧ (q.digit k : ℕ) = 0 := by
    have ⟨hp_digit, hq_digit⟩ := hdigit_ge_N k hk
    have hp_val : (p.digit k : ℕ) = 0 := by
      calc
        (p.digit k : ℕ) = Digit.toNat (p.digit k) := rfl
        _ = Digit.toNat (0 : Digit) := by rw [hp_digit]
        _ = 0 := rfl
    have hq_val : (q.digit k : ℕ) = 0 := by
      calc
        (q.digit k : ℕ) = Digit.toNat (q.digit k) := rfl
        _ = Digit.toNat (0 : Digit) := by rw [hq_digit]
        _ = 0 := rfl
    exact ⟨hp_val, hq_val⟩
  have hcarry_prep : ∀ n, p.carry q (N+1 + n) = 0 := by
    intro n
    induction' n with m ih
    · rw [carry_succ p q N]
      have ⟨hp_val, hq_val⟩ := digit_val_zero N (le_refl N)
      have hcarry_le1 : p.carry q N ≤ 1 := carry_le_one _ _ _
      have hsum : ((p.digit N : ℕ) + (q.digit N : ℕ) + p.carry q N) < 10 := by
        rw [hp_val, hq_val]
        omega
      simp [hsum]
    · have h_eq : N+1+(m+1) = (N+1+m)+1 := by omega
      rw [h_eq, carry_succ p q (N+1+m), ih]
      have ⟨hp_val, hq_val⟩ := digit_val_zero (N+1+m) (by omega)
      simp [hp_val, hq_val]
  have hcarry_gt_N : ∀ k > N, p.carry q k = 0 := by
    intro k hk
    have : N+1 + (k - (N+1)) = k := by omega
    rw [← this]
    apply hcarry_prep
  intro i hi
  split at hi
  · -- case: carry N = 1, sum_digit_top = N, need i > N
    have hi_gt_N : i > N := by omega
    have hcarry_i : p.carry q i = 0 := hcarry_gt_N i hi_gt_N
    have ⟨hp_val, hq_val⟩ := digit_val_zero i (by omega)
    unfold sum_digit
    rw [hp_val, hq_val, hcarry_i]
    norm_num
  · -- case: carry N ≠ 1, sum_digit_top = N-1, need i > N-1
    have hi_ge_N : i ≥ N := by omega
    have hcarry_i : p.carry q i = 0 := by
      by_cases hi_eq_N : i = N
      · subst hi_eq_N
        have hcarry0 : p.carry q N = 0 := by
          have hle : p.carry q N ≤ 1 := carry_le_one _ _ _
          omega
        exact hcarry0
      · have hi_gt_N : i > N := by omega
        exact hcarry_gt_N i hi_gt_N
    have ⟨hp_val, hq_val⟩ := digit_val_zero i hi_ge_N
    unfold sum_digit
    rw [hp_val, hq_val, hcarry_i]
    norm_num


/-- The decimal list for the sum of p and q. -/
def PosintDecimal.longAddition (p q : PosintDecimal) : PosintDecimal where
  digits := (List.range (p.sum_digit_top q + 1)).reverse.map (λ i =>
    Digit.mk (h := sum_digit_lt p q i))
  nonempty := by
    dsimp
    simp
  nonzero := by
    dsimp
    have hhead : ((List.range (p.sum_digit_top q + 1)).reverse.map (λ i =>
      Digit.mk (h := sum_digit_lt p q i))).head (by simp) =
      Digit.mk (h := sum_digit_lt p q (p.sum_digit_top q)) := by
      simp
    rw [hhead]
    intro hzero
    apply leading_nonzero p q
    have hval : (Digit.mk (h := sum_digit_lt p q (p.sum_digit_top q)) : ℕ) =
      p.sum_digit q (p.sum_digit_top q) := by simp
    simpa [hval] using congrArg (λ d : Digit => (d : ℕ)) hzero

theorem PosintDecimal.sum_eq (p q:PosintDecimal) (i:ℕ) :
    (((p.longAddition q).digit i):ℕ) = p.sum_digit q i ∧ (p.longAddition q:ℕ) = p + q := by
  sorry
