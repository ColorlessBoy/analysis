import Analysis.MeasureTheory.Section_1_2_3
import Analysis.Misc.NatBitwise

/-!
# Introduction to Measure Theory, Section 1.3.1: Integration of simple functions

A companion to (the introduction to) Section 1.3.1 of the book "An introduction to Measure Theory".

-/

-- some tools to convert between EReal-valued, ℝ-valued, and ℂ-valued functions

def EReal.abs_fun {X Y:Type*} [RCLike Y] (f: X → Y) : X → EReal := fun x ↦ ‖f x‖.toEReal
def Complex.re_fun {X:Type*} (f: X → ℂ) : X → ℝ := fun x ↦ Complex.re (f x)
def Complex.im_fun {X:Type*} (f: X → ℂ) : X → ℝ := fun x ↦ Complex.im (f x)
def Complex.conj_fun {X:Type*} (f: X → ℂ) : X → ℂ := fun x ↦ starRingEnd ℂ (f x)
def EReal.pos_fun {X:Type*} (f: X → ℝ) : X → EReal := fun x ↦ (max (f x) 0).toEReal
def EReal.neg_fun {X:Type*} (f: X → ℝ) : X → EReal := fun x ↦ (max (-f x) 0).toEReal
def Real.complex_fun {X:Type*} (f: X → ℝ) : X → ℂ := fun x ↦ Complex.ofReal (f x)
def Real.EReal_fun {X:Type*} (f: X → ℝ) : X → EReal := fun x ↦ Real.toEReal (f x)

noncomputable def EReal.indicator {X:Type*} (A: Set X) : X → EReal := Real.EReal_fun A.indicator'

theorem EReal.indicator_of_mem {X:Type*} {A: Set X} {x:X} (h: x ∈ A) : EReal.indicator A x = 1 := by
  simp [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem h]

theorem EReal.indicator_of_notMem {X:Type*} {A: Set X} {x:X} (h: x ∉ A) : EReal.indicator A x = 0 := by
  simp [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem h]

noncomputable def Complex.indicator {X:Type*} (A: Set X) : X → ℂ := Real.complex_fun A.indicator'

/-- Definition 1.3.2 -/
def UnsignedSimpleFunction {d:ℕ} (f: EuclideanSpace' d → EReal) : Prop := ∃ (k:ℕ) (c: Fin k → EReal) (E: Fin k → Set (EuclideanSpace' d)),
  (∀ i, LebesgueMeasurable (E i) ∧ c i ≥ 0) ∧ f = ∑ i, (c i) • (EReal.indicator (E i))

def RealSimpleFunction {d:ℕ} (f: EuclideanSpace' d → ℝ) : Prop := ∃ (k:ℕ) (c: Fin k → ℝ) (E: Fin k → Set (EuclideanSpace' d)),
  (∀ i, LebesgueMeasurable (E i)) ∧ f = ∑ i, (c i) • (E i).indicator'

def ComplexSimpleFunction {d:ℕ} (f: EuclideanSpace' d → ℂ) : Prop := ∃ (k:ℕ) (c: Fin k → ℂ) (E: Fin k → Set (EuclideanSpace' d)),
  (∀ i, LebesgueMeasurable (E i)) ∧ f = ∑ i, (c i) • (Complex.indicator (E i))

-- TODO: coercions between these concepts, and vector space structure on real and complex simple functions (and cone structure on unsigned simple functions).


@[coe]
abbrev RealSimpleFunction.toComplex {d:ℕ} (f: EuclideanSpace' d → ℝ) (df: RealSimpleFunction f) : ComplexSimpleFunction (Real.complex_fun f) := by
  obtain ⟨k, c, E, hmes, heq⟩ := df
  use k, fun i => Complex.ofReal (c i), E
  constructor
  · exact hmes
  · ext x
    simp only [Real.complex_fun, Complex.indicator, heq]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Complex.ofReal_sum]
    congr 1
    ext i
    exact Complex.ofReal_mul (c i) ((E i).indicator' x)

instance RealSimpleFunction.coe_complex {d:ℕ} (f: EuclideanSpace' d → ℝ) : Coe (RealSimpleFunction f) (ComplexSimpleFunction (Real.complex_fun f)) := {
  coe := RealSimpleFunction.toComplex f
}


lemma UnsignedSimpleFunction.add {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g) : UnsignedSimpleFunction (f + g) := by
  obtain ⟨k₁, c₁, E₁, ⟨hmes₁, heq₁⟩⟩ := hf
  obtain ⟨k₂, c₂, E₂, ⟨hmes₂, heq₂⟩⟩ := hg
  use k₁ + k₂, fun i => if h : i < k₁ then c₁ ⟨i, h⟩ else c₂ ⟨i - k₁, by omega⟩,
       fun i => if h : i < k₁ then E₁ ⟨i, h⟩ else E₂ ⟨i - k₁, by omega⟩
  constructor
  · intro i
    split_ifs with h
    · exact hmes₁ ⟨i, h⟩
    · exact hmes₂ ⟨i - k₁, by omega⟩
  · ext x
    rw [heq₁, heq₂]
    simp [Fin.sum_univ_add]

private lemma EReal.indicator_nonneg' {X:Type*} (A: Set X) (x : X) : 0 ≤ EReal.indicator A x := by
  simp only [EReal.indicator, Real.EReal_fun]
  exact EReal.coe_nonneg.mpr (Set.indicator_nonneg (fun _ _ => zero_le_one) x)

lemma UnsignedSimpleFunction.smul {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) {a: EReal} (ha: a ≥ 0) : UnsignedSimpleFunction (a • f) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hf
  use k, fun i => a * (c i), E
  constructor
  · intro i
    exact ⟨hmes i |>.1, mul_nonneg ha (hmes i |>.2)⟩
  · rw [heq]
    ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [EReal.mul_finset_sum_of_nonneg k a (fun i => (c i) * EReal.indicator (E i) x)
        (fun i => mul_nonneg (hmes i |>.2) (EReal.indicator_nonneg' (E i) x))]
    congr 1
    ext i
    rw [mul_assoc]

lemma RealSimpleFunction.add {d:ℕ} {f g: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) (hg: RealSimpleFunction g) : RealSimpleFunction (f + g) := by
  obtain ⟨k₁, c₁, E₁, ⟨hmes₁, heq₁⟩⟩ := hf
  obtain ⟨k₂, c₂, E₂, ⟨hmes₂, heq₂⟩⟩ := hg
  use k₁ + k₂, fun i => if h : i < k₁ then c₁ ⟨i, h⟩ else c₂ ⟨i - k₁, by omega⟩,
       fun i => if h : i < k₁ then E₁ ⟨i, h⟩ else E₂ ⟨i - k₁, by omega⟩
  constructor
  · intro i
    split_ifs with h
    · exact hmes₁ ⟨i, h⟩
    · exact hmes₂ ⟨i - k₁, by omega⟩
  · ext x
    rw [heq₁, heq₂]
    simp [Fin.sum_univ_add]

lemma ComplexSimpleFunction.add {d:ℕ} {f g: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) (hg: ComplexSimpleFunction g) : ComplexSimpleFunction (f + g) := by
  obtain ⟨k₁, c₁, E₁, ⟨hmes₁, heq₁⟩⟩ := hf
  obtain ⟨k₂, c₂, E₂, ⟨hmes₂, heq₂⟩⟩ := hg
  use k₁ + k₂, fun i => if h : i < k₁ then c₁ ⟨i, h⟩ else c₂ ⟨i - k₁, by omega⟩,
       fun i => if h : i < k₁ then E₁ ⟨i, h⟩ else E₂ ⟨i - k₁, by omega⟩
  constructor
  · intro i
    split_ifs with h
    · exact hmes₁ ⟨i, h⟩
    · exact hmes₂ ⟨i - k₁, by omega⟩
  · ext x
    rw [heq₁, heq₂]
    simp [Fin.sum_univ_add]

lemma RealSimpleFunction.smul {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) (a: ℝ)  : RealSimpleFunction (a • f) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hf
  use k, fun i => a * (c i), E
  constructor
  · intro i
    exact hmes i
  · rw [heq]
    ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    ext i
    rw [mul_assoc]

lemma ComplexSimpleFunction.smul {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) (a: ℂ)  : ComplexSimpleFunction (a • f) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hf
  use k, fun i => a * (c i), E
  constructor
  · intro i
    exact hmes i
  · rw [heq]
    ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    congr 1
    ext i
    rw [mul_assoc]

private lemma Complex.indicator_conj {X:Type*} (A: Set X) (x : X) :
    starRingEnd ℂ (Complex.indicator A x) = Complex.indicator A x := by
  simp only [Complex.indicator, Real.complex_fun]
  exact Complex.conj_ofReal _

lemma ComplexSimpleFunction.conj {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : ComplexSimpleFunction (Complex.conj_fun f) := by
  obtain ⟨k, c, E, ⟨hmes, heq⟩⟩ := hf
  use k, fun i => starRingEnd ℂ (c i), E
  constructor
  · intro i
    exact hmes i
  · rw [heq]
    ext x
    simp only [Complex.conj_fun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [map_sum]
    congr 1
    ext i
    rw [map_mul, Complex.indicator_conj]

noncomputable def UnsignedSimpleFunction.integ {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) : EReal := ∑ i, (hf.choose_spec.choose i) * Lebesgue_measure (hf.choose_spec.choose_spec.choose i)

/-! ## Helper lemmas for Lemma 1.3.4

The proof uses a Venn diagram argument: given two representations of the same simple function,
we partition R^d into atoms (intersections of all sets and their complements), express each
original set as a disjoint union of atoms, and use finite additivity of Lebesgue measure.
-/

namespace UnsignedSimpleFunction.IntegralWellDef

open scoped Classical

/-- {given -show}`k, k'` Given families of sets indexed by {lean}`Fin k` and {lean}`Fin k'`, an atom is determined by
    a choice of “in” or “out” for each set. We encode this as a {lean}`Fin (2^(k+k'))` index. -/
def atomMembership (_k _k' : ℕ) (n : ℕ) (i : ℕ) : Bool := (n / 2^i) % 2 = 1

lemma atomMembership_eq_testBit (k k' n i : ℕ) : atomMembership k k' n i = n.testBit i := by
  simp only [atomMembership, Nat.testBit_eq_decide_div_mod_eq]

/-- The atom indexed by n is the intersection over all $`i` of ($`E_i` if bit $`i` is 1, else $`E_i^c`) -/
def atom {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (n : Fin (2^(k+k'))) : Set X :=
  {x | (∀ i : Fin k, atomMembership k k' n i ↔ x ∈ E i) ∧
       (∀ i : Fin k', atomMembership k k' n (k + i) ↔ x ∈ E' i)}

/-- Atoms are pairwise disjoint -/
lemma atom_pairwiseDisjoint {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) :
    Set.univ.PairwiseDisjoint (atom E E') := by
  intro i _ j _ hij
  simp only [Function.onFun]
  rw [Set.disjoint_left]
  intro x hxi hxj
  simp only [atom, Set.mem_setOf_eq, atomMembership_eq_testBit] at hxi hxj
  -- If i ≠ j, they differ in some bit
  have hne : i.val ≠ j.val := Fin.val_ne_of_ne hij
  obtain ⟨bit, hbit⟩ := Nat.exists_testBit_ne_of_ne hne
  -- The bit must be < k + k' since both i, j < 2^(k+k')
  have hi_lt : i.val < 2^(k + k') := i.isLt
  have hj_lt : j.val < 2^(k + k') := j.isLt
  have hbit_bound : bit < k + k' := by
    by_contra h
    push_neg at h
    have hi_false : i.val.testBit bit = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hi_lt (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h))
    have hj_false : j.val.testBit bit = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hj_lt (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) h))
    exact hbit (hi_false.trans hj_false.symm)
  -- Now we know bit < k + k', so it indexes into E or E'
  by_cases hbit_k : bit < k
  · -- bit indexes into E
    have hi_iff := hxi.1 ⟨bit, hbit_k⟩
    have hj_iff := hxj.1 ⟨bit, hbit_k⟩
    -- hxi and hxj both give x ∈ E ⟨bit, _⟩ ↔ testBit = true
    -- But i and j have different bits, so one says x ∈ E and the other says x ∉ E
    cases h_i : i.val.testBit bit <;> cases h_j : j.val.testBit bit
    · exact hbit (h_i.trans h_j.symm)
    · have hx_in : x ∈ E ⟨bit, hbit_k⟩ := hj_iff.mp h_j
      have hx_out : x ∉ E ⟨bit, hbit_k⟩ := fun h => by simp [hi_iff.mpr h] at h_i
      exact hx_out hx_in
    · have hx_in : x ∈ E ⟨bit, hbit_k⟩ := hi_iff.mp h_i
      have hx_out : x ∉ E ⟨bit, hbit_k⟩ := fun h => by simp [hj_iff.mpr h] at h_j
      exact hx_out hx_in
    · exact hbit (h_i.trans h_j.symm)
  · -- bit indexes into E' (bit ∈ [k, k+k'))
    have hbit_k' : bit - k < k' := by omega
    have h_add : k + (bit - k) = bit := by omega
    have hi_iff := hxi.2 ⟨bit - k, hbit_k'⟩
    have hj_iff := hxj.2 ⟨bit - k, hbit_k'⟩
    simp only [h_add] at hi_iff hj_iff
    cases h_i : i.val.testBit bit <;> cases h_j : j.val.testBit bit
    · exact hbit (h_i.trans h_j.symm)
    · have hx_in : x ∈ E' ⟨bit - k, hbit_k'⟩ := hj_iff.mp h_j
      have hx_out : x ∉ E' ⟨bit - k, hbit_k'⟩ := fun h => by simp [hi_iff.mpr h] at h_i
      exact hx_out hx_in
    · have hx_in : x ∈ E' ⟨bit - k, hbit_k'⟩ := hi_iff.mp h_i
      have hx_out : x ∉ E' ⟨bit - k, hbit_k'⟩ := fun h => by simp [hj_iff.mpr h] at h_j
      exact hx_out hx_in
    · exact hbit (h_i.trans h_j.symm)

/-- Sum of powers of 2 up to n equals 2^n - 1 -/
private lemma sum_pow_two_range (n : ℕ) : ∑ i ∈ Finset.range n, (2:ℕ)^i = 2^n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have h : 1 ≤ 2^n := Nat.one_le_two_pow
    omega

/-- For any subset of {lean}`Fin k`, sum of {given -show (type := "Fin k")}`j` {lean}`2^j.val` is less than {lean}`2^k` -/
private lemma sum_pow_two_fin_lt {k : ℕ} {s : Finset (Fin k)} :
    s.sum (fun j => (2:ℕ)^j.val) < 2^k := by
  have h1 : s.sum (fun j => (2:ℕ)^j.val) ≤ Finset.univ.sum (fun j : Fin k => (2:ℕ)^j.val) := by
    apply Finset.sum_le_sum_of_subset
    exact Finset.subset_univ s
  have h2 : Finset.univ.sum (fun j : Fin k => (2:ℕ)^j.val) = ∑ i ∈ Finset.range k, 2^i := by
    rw [Fin.sum_univ_eq_sum_range]
  have h3 : ∑ i ∈ Finset.range k, (2:ℕ)^i = 2^k - 1 := sum_pow_two_range k
  have h4 : 2^k - 1 < 2^k := Nat.sub_lt Nat.one_le_two_pow Nat.one_pos
  omega

/-- Helper: construct atom index from membership pattern.
    The atom index encodes x's membership in each set as bits. -/
noncomputable def atomIndexOf {X : Type*} [DecidableEq X] {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) : ℕ :=
  (Finset.univ.filter fun j : Fin k => x ∈ E j).sum (fun j => 2^j.val) +
  (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => 2^(k + j'.val))

/-- The atom index is bounded by 2^(k+k') -/
lemma atomIndexOf_lt {X : Type*} [DecidableEq X] {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) :
    atomIndexOf E E' x < 2^(k+k') := by
  unfold atomIndexOf
  have hpart1 : (Finset.univ.filter fun j : Fin k => x ∈ E j).sum (fun j => (2:ℕ)^j.val) < 2^k :=
    sum_pow_two_fin_lt
  have hpart2_inner : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) < 2^k' :=
    sum_pow_two_fin_lt
  have hrw : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^(k + j'.val)) =
             2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) := by
    rw [Finset.mul_sum]
    congr 1; ext j'; rw [pow_add]
  rw [hrw]
  have h2k_pos : 0 < 2^k := Nat.two_pow_pos k
  have hpart2 : 2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) < 2^(k+k') := by
    calc 2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val)
        < 2^k * 2^k' := (Nat.mul_lt_mul_left h2k_pos).mpr hpart2_inner
      _ = 2^(k+k') := by rw [← pow_add]
  -- Use tight bounds: sum1 ≤ 2^k - 1, sum2 ≤ 2^k * (2^k' - 1) = 2^(k+k') - 2^k
  -- So sum1 + sum2 ≤ (2^k - 1) + (2^(k+k') - 2^k) = 2^(k+k') - 1 < 2^(k+k')
  have hpart1_le : (Finset.univ.filter fun j : Fin k => x ∈ E j).sum (fun j => (2:ℕ)^j.val) ≤ 2^k - 1 :=
    Nat.le_sub_one_of_lt hpart1
  have hpart2_le : 2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) ≤ 2^(k+k') - 2^k := by
    have inner_le : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) ≤ 2^k' - 1 :=
      Nat.le_sub_one_of_lt hpart2_inner
    calc 2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val)
        ≤ 2^k * (2^k' - 1) := Nat.mul_le_mul_left _ inner_le
      _ = 2^k * 2^k' - 2^k := by rw [Nat.mul_sub_one]
      _ = 2^(k+k') - 2^k := by rw [pow_add]
  have h2k_le : 2^k ≤ 2^(k+k') := Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right k k')
  calc (Finset.univ.filter fun j : Fin k => x ∈ E j).sum (fun j => (2:ℕ)^j.val) +
       2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val)
      ≤ (2^k - 1) + (2^(k+k') - 2^k) := Nat.add_le_add hpart1_le hpart2_le
    _ = 2^(k+k') - 1 := by omega
    _ < 2^(k+k') := Nat.sub_lt (Nat.two_pow_pos _) (by norm_num)

/-- The atom index has bit j set iff x ∈ E j -/
lemma atomIndexOf_testBit_E {X : Type*} [DecidableEq X] {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) (j : Fin k) :
    (atomIndexOf E E' x).testBit j.val ↔ x ∈ E j := by
  unfold atomIndexOf
  -- atomIndexOf = Part1 + Part2 where Part2 = 2^k * (inner sum)
  have hrw : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^(k + j'.val)) =
             2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) := by
    rw [Finset.mul_sum]; congr 1; ext j'; rw [pow_add]
  rw [hrw]
  -- Use testBit_two_pow_mul_add: for j.val < k and Part1 < 2^k, testBit j only looks at Part1
  have hpart1_lt : (Finset.univ.filter fun i : Fin k => x ∈ E i).sum (fun i => (2:ℕ)^i.val) < 2^k :=
    sum_pow_two_fin_lt
  rw [add_comm, Nat.testBit_two_pow_mul_add _ hpart1_lt, if_pos j.isLt]
  -- Now show: Part1.testBit j.val ↔ x ∈ E j
  rw [Nat.testBit_sum_pow_two_fin]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The atom index has bit (k+j) set iff x ∈ E' j -/
lemma atomIndexOf_testBit_E' {X : Type*} [DecidableEq X] {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (x : X) (j : Fin k') :
    (atomIndexOf E E' x).testBit (k + j.val) ↔ x ∈ E' j := by
  unfold atomIndexOf
  have hrw : (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^(k + j'.val)) =
             2^k * (Finset.univ.filter fun j' : Fin k' => x ∈ E' j').sum (fun j' => (2:ℕ)^j'.val) := by
    rw [Finset.mul_sum]; congr 1; ext j'; rw [pow_add]
  rw [hrw]
  -- Use testBit_two_pow_mul_add: for k + j.val ≥ k and Part1 < 2^k
  have hpart1_lt : (Finset.univ.filter fun i : Fin k => x ∈ E i).sum (fun i => (2:ℕ)^i.val) < 2^k :=
    sum_pow_two_fin_lt
  rw [add_comm, Nat.testBit_two_pow_mul_add _ hpart1_lt]
  have hge : ¬ (k + j.val < k) := by omega
  rw [if_neg hge]
  -- Now show: Part2_inner.testBit ((k + j.val) - k) ↔ x ∈ E' j
  have hsub : (k + j.val) - k = j.val := Nat.add_sub_cancel_left k j.val
  rw [hsub, Nat.testBit_sum_pow_two_fin]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- Original set E\_i is the union of atoms where bit i is 1 -/
lemma set_eq_biUnion_atoms {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (i : Fin k) :
    E i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n i}, atom E E' n := by
  classical
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    -- Construct the atom index from x's membership pattern
    let n : Fin (2^(k+k')) := ⟨atomIndexOf E E' x, atomIndexOf_lt E E' x⟩
    refine ⟨n, ?_, ?_⟩
    · -- Show atomMembership k k' n i = true
      rw [atomMembership_eq_testBit]
      simp only [n, atomIndexOf_testBit_E E E' x i]
      exact hx
    · -- Show x ∈ atom E E' n
      simp only [atom, Set.mem_setOf_eq, n]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E E E' x j]
      · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E' E E' x j]
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
    obtain ⟨n, hn_bit, hx_atom⟩ := hx
    exact (hx_atom.1 i).mp hn_bit

/-- Original set E'\_i is the union of atoms where bit (k+i) is 1 -/
lemma set_eq_biUnion_atoms' {X : Type*} {k k' : ℕ} (E : Fin k → Set X) (E' : Fin k' → Set X) (i : Fin k') :
    E' i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n (k + i)}, atom E E' n := by
  classical
  ext x
  constructor
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    let n : Fin (2^(k+k')) := ⟨atomIndexOf E E' x, atomIndexOf_lt E E' x⟩
    refine ⟨n, ?_, ?_⟩
    · rw [atomMembership_eq_testBit]
      simp only [n, atomIndexOf_testBit_E' E E' x i]
      exact hx
    · simp only [atom, Set.mem_setOf_eq, n]
      refine ⟨fun j => ?_, fun j => ?_⟩
      · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E E E' x j]
      · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E' E E' x j]
  · intro hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hx
    obtain ⟨n, hn_bit, hx_atom⟩ := hx
    exact (hx_atom.2 i).mp hn_bit

/-- Atoms are measurable if the original sets are -/
lemma atom_measurable {d k k' : ℕ} {E : Fin k → Set (EuclideanSpace' d)} {E' : Fin k' → Set (EuclideanSpace' d)}
    (hE : ∀ i, LebesgueMeasurable (E i)) (hE' : ∀ i, LebesgueMeasurable (E' i)) (n : Fin (2^(k+k'))) :
    LebesgueMeasurable (atom E E' n) := by
  -- The atom is an intersection of sets of the form E_i or (E_i)ᶜ
  -- Rewrite atom as intersection
  have hatom_eq : atom E E' n =
      (⋂ i : Fin k, if atomMembership k k' n i then E i else (E i)ᶜ) ∩
      (⋂ i : Fin k', if atomMembership k k' n (k + i) then E' i else (E' i)ᶜ) := by
    ext x
    simp only [atom, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro ⟨h1, h2⟩
      constructor
      · intro i
        by_cases hbit : atomMembership k k' n i
        · simp only [hbit, ↓reduceIte]
          exact (h1 i).mp hbit
        · simp only [hbit]
          exact fun hx => hbit ((h1 i).mpr hx)
      · intro i
        by_cases hbit : atomMembership k k' n (k + i)
        · simp only [hbit, ↓reduceIte]
          exact (h2 i).mp hbit
        · simp only [hbit]
          exact fun hx => hbit ((h2 i).mpr hx)
    · intro ⟨h1, h2⟩
      constructor
      · intro i
        specialize h1 i
        by_cases hbit : atomMembership k k' n i
        · simp only [hbit, ↓reduceIte] at h1
          exact ⟨fun _ => h1, fun _ => hbit⟩
        · simp only [hbit] at h1
          exact ⟨fun hf => (hbit hf).elim, fun hx => (h1 hx).elim⟩
      · intro i
        specialize h2 i
        by_cases hbit : atomMembership k k' n (k + i)
        · simp only [hbit, ↓reduceIte] at h2
          exact ⟨fun _ => h2, fun _ => hbit⟩
        · simp only [hbit] at h2
          exact ⟨fun hf => (hbit hf).elim, fun hx => (h2 hx).elim⟩
  rw [hatom_eq]
  -- Now show the intersection is measurable
  -- Each component is E i or (E i)ᶜ, both measurable
  -- Finite intersection of measurable sets is measurable
  apply LebesgueMeasurable.inter
  · -- First part: ⋂ i : Fin k, ... (finite intersection of measurable sets)
    apply LebesgueMeasurable.finite_inter
    intro i
    by_cases h : atomMembership k k' n i
    · simp only [h]; exact hE i
    · simp only [h]; exact (hE i).complement
  · -- Second part: ⋂ i : Fin k', ... (finite intersection of measurable sets)
    apply LebesgueMeasurable.finite_inter
    intro i
    by_cases h : atomMembership k k' n (k + i)
    · simp only [h]; exact hE' i
    · simp only [h]; exact (hE' i).complement

/-- Indicator function evaluates to c if x ∈ E -/
lemma indicator_mul_mem {d : ℕ} (E : Set (EuclideanSpace' d)) (c : EReal) (x : EuclideanSpace' d)
    (h : x ∈ E) : c * (EReal.indicator E x) = c := by
  simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem h, EReal.coe_one, mul_one]

/-- Indicator function evaluates to 0 if x ∉ E -/
lemma indicator_mul_not_mem {d : ℕ} (E : Set (EuclideanSpace' d)) (c : EReal) (x : EuclideanSpace' d)
    (h : x ∉ E) : c * (EReal.indicator E x) = 0 := by
  simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem h, EReal.coe_zero, mul_zero]

/-- The weighted measure sum for a representation -/
noncomputable def weightedMeasureSum {d k : ℕ} (c : Fin k → EReal) (E : Fin k → Set (EuclideanSpace' d)) : EReal :=
  ∑ i, (c i) * Lebesgue_measure (E i)

/-- Core lemma: Two representations of the same function give the same weighted measure sum.
    This is the heart of Lemma 1.3.4 (Venn diagram argument). -/
lemma weightedMeasureSum_eq_of_eq {d k k' : ℕ}
    {c : Fin k → EReal} {E : Fin k → Set (EuclideanSpace' d)}
    {c' : Fin k' → EReal} {E' : Fin k' → Set (EuclideanSpace' d)}
    (hmes : ∀ i, LebesgueMeasurable (E i)) (hmes' : ∀ i, LebesgueMeasurable (E' i))
    (hnonneg : ∀ i, c i ≥ 0) (hnonneg' : ∀ i, c' i ≥ 0)
    (heq : ∑ i, (c i) • (EReal.indicator (E i)) = ∑ i, (c' i) • (EReal.indicator (E' i))) :
    weightedMeasureSum c E = weightedMeasureSum c' E' := by
  -- The proof uses the Venn diagram/atom argument
  -- 1. For any x in a non-empty atom A_n, evaluate heq at x:
  --    sum_{i : x ∈ E_i} c_i = sum_{j : x ∈ E'_j} c'_j
  -- 2. The membership in E_i for x ∈ A_n is determined by bit i of n
  -- 3. Multiply by m(A_n) and sum over all atoms
  -- 4. Swap order of summation to get the result

  -- Define atom measures
  let atomMeas : Fin (2^(k+k')) → EReal := fun n => Lebesgue_measure (atom E E' n)

  -- Atoms are measurable
  have hatom_mes : ∀ n, LebesgueMeasurable (atom E E' n) := atom_measurable hmes hmes'

  -- Step 1: For any point in an atom, the pointwise sums are equal
  have hpoint : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n,
      ∑ i : Fin k, (c i) * (EReal.indicator (E i) x) = ∑ i : Fin k', (c' i) * (EReal.indicator (E' i) x) := by
    intro n x hx
    have := congr_fun heq x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this

  -- Step 2: In atom n, membership in E_i is determined by bit i
  have hmem_E : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n, ∀ i : Fin k,
      (x ∈ E i) ↔ atomMembership k k' n i := by
    intro n x hx i
    exact (hx.1 i).symm

  have hmem_E' : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n, ∀ i : Fin k',
      (x ∈ E' i) ↔ atomMembership k k' n (k + i) := by
    intro n x hx i
    exact (hx.2 i).symm

  -- Step 3: The pointwise sum simplifies based on bit pattern
  have hsum_simp : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n,
      ∑ i : Fin k, (c i) * (EReal.indicator (E i) x) = ∑ i : Fin k, if atomMembership k k' n i then c i else 0 := by
    intro n x hx
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : atomMembership k k' n i
    · simp only [h]
      have hx_in : x ∈ E i := (hmem_E n x hx i).mpr h
      exact indicator_mul_mem (E i) (c i) x hx_in
    · simp only [h]
      have hx_out : x ∉ E i := fun hc => h ((hmem_E n x hx i).mp hc)
      exact indicator_mul_not_mem (E i) (c i) x hx_out

  have hsum_simp' : ∀ n : Fin (2^(k+k')), ∀ x ∈ atom E E' n,
      ∑ i : Fin k', (c' i) * (EReal.indicator (E' i) x) = ∑ i : Fin k', if atomMembership k k' n (k + i) then c' i else 0 := by
    intro n x hx
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : atomMembership k k' n (k + i)
    · simp only [h]
      have hx_in : x ∈ E' i := (hmem_E' n x hx i).mpr h
      exact indicator_mul_mem (E' i) (c' i) x hx_in
    · simp only [h]
      have hx_out : x ∉ E' i := fun hc => h ((hmem_E' n x hx i).mp hc)
      exact indicator_mul_not_mem (E' i) (c' i) x hx_out

  -- Step 4: For non-empty atoms, the bit-pattern sums are equal
  have hbit_eq : ∀ n : Fin (2^(k+k')), (atom E E' n).Nonempty →
      (∑ i : Fin k, if atomMembership k k' n i = true then c i else 0 : EReal) =
      (∑ i : Fin k', if atomMembership k k' n (k + i) = true then c' i else 0 : EReal) := by
    intro n ⟨x, hx⟩
    rw [← hsum_simp n x hx, ← hsum_simp' n x hx]
    exact hpoint n x hx

  -- Step 5: E_i = union of atoms where bit i = 1
  have hE_decomp : ∀ i : Fin k, E i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n i}, atom E E' n :=
    fun i => set_eq_biUnion_atoms E E' i

  -- Step 6: Use finite additivity (this requires showing atoms are disjoint and measurable)
  -- m(E_i) = sum over atoms where bit i = 1 of m(atom)
  have hmes_decomp : ∀ i : Fin k, Lebesgue_measure (E i) =
      ∑ n : Fin (2^(k+k')), if atomMembership k k' n i then atomMeas n else 0 := by
    intro i
    -- Define a modified atom family: atom' n = atom n if bit i is 1, else ∅
    let atom' : Fin (2^(k+k')) → Set (EuclideanSpace' d) := fun n =>
      if atomMembership k k' n i then atom E E' n else ∅
    -- E i = ⋃ n, atom' n (because atoms with bit 0 contribute nothing)
    have hE_eq : E i = ⋃ n, atom' n := by
      rw [hE_decomp i]
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro ⟨n, hn, hx⟩
        use n
        simp only [atom', hn, ite_true]
        exact hx
      · intro ⟨n, hx⟩
        simp only [atom'] at hx
        by_cases hn : atomMembership k k' n i
        · simp only [hn, ite_true] at hx
          exact ⟨n, hn, hx⟩
        · simp only [hn] at hx
          exact False.elim hx
    -- atom' is pairwise disjoint
    have hdisj' : Set.univ.PairwiseDisjoint atom' := by
      intro i₁ _ i₂ _ hi
      simp only [Function.onFun, atom']
      by_cases h1 : atomMembership k k' i₁ i <;> by_cases h2 : atomMembership k k' i₂ i
      · simp only [h1, h2, ite_true]
        exact atom_pairwiseDisjoint E E' (by trivial : i₁ ∈ Set.univ) (by trivial) hi
      · simp only [h1, h2, ite_true]
        rw [Set.disjoint_left]; intro _ _; simp
      · simp only [h1, h2, ite_true]
        rw [Set.disjoint_left]; simp
      · simp only [h1, h2]
        rw [Set.disjoint_left]; simp
    -- atom' is measurable
    have hmes'_atom : ∀ n, LebesgueMeasurable (atom' n) := by
      intro n
      simp only [atom']
      by_cases h : atomMembership k k' n i
      · simp only [h, ite_true]; exact hatom_mes n
      · simp only [h]; exact LebesgueMeasurable.empty
    -- Apply finite additivity
    calc Lebesgue_measure (E i) = Lebesgue_measure (⋃ n, atom' n) := by rw [hE_eq]
      _ = ∑' n, Lebesgue_measure (atom' n) := Lebesgue_measure.finite_union hmes'_atom hdisj'
      _ = ∑ n : Fin (2^(k+k')), Lebesgue_measure (atom' n) := tsum_fintype _
      _ = ∑ n : Fin (2^(k+k')), if atomMembership k k' n i then atomMeas n else 0 := by
          congr 1; funext n; simp only [atom']
          by_cases h : atomMembership k k' n i
          · simp only [h, ite_true]; rfl
          · simp only [h]; exact Lebesgue_measure.empty

  have hE'_decomp : ∀ i : Fin k', E' i = ⋃ n ∈ {n : Fin (2^(k+k')) | atomMembership k k' n (k + i)}, atom E E' n :=
    fun i => set_eq_biUnion_atoms' E E' i

  have hmes_decomp' : ∀ i : Fin k', Lebesgue_measure (E' i) =
      ∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then atomMeas n else 0 := by
    intro i
    let atom'' : Fin (2^(k+k')) → Set (EuclideanSpace' d) := fun n =>
      if atomMembership k k' n (k + i) then atom E E' n else ∅
    have hE'_eq : E' i = ⋃ n, atom'' n := by
      rw [hE'_decomp i]
      ext x
      simp only [Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · intro ⟨n, hn, hx⟩
        use n
        simp only [atom'', hn, ite_true]
        exact hx
      · intro ⟨n, hx⟩
        simp only [atom''] at hx
        by_cases hn : atomMembership k k' n (k + i)
        · simp only [hn, ite_true] at hx
          exact ⟨n, hn, hx⟩
        · simp only [hn] at hx
          exact False.elim hx
    have hdisj'' : Set.univ.PairwiseDisjoint atom'' := by
      intro i₁ _ i₂ _ hi
      simp only [Function.onFun, atom'']
      by_cases h1 : atomMembership k k' i₁ (k + i) <;> by_cases h2 : atomMembership k k' i₂ (k + i)
      · simp only [h1, h2, ite_true]
        exact atom_pairwiseDisjoint E E' (by trivial : i₁ ∈ Set.univ) (by trivial) hi
      · simp only [h1, h2, ite_true]
        rw [Set.disjoint_left]; intro _ _; simp
      · simp only [h1, h2, ite_true]
        rw [Set.disjoint_left]; simp
      · simp only [h1, h2]
        rw [Set.disjoint_left]; simp
    have hmes''_atom : ∀ n, LebesgueMeasurable (atom'' n) := by
      intro n
      simp only [atom'']
      by_cases h : atomMembership k k' n (k + i)
      · simp only [h, ite_true]; exact hatom_mes n
      · simp only [h]; exact LebesgueMeasurable.empty
    calc Lebesgue_measure (E' i) = Lebesgue_measure (⋃ n, atom'' n) := by rw [hE'_eq]
      _ = ∑' n, Lebesgue_measure (atom'' n) := Lebesgue_measure.finite_union hmes''_atom hdisj''
      _ = ∑ n : Fin (2^(k+k')), Lebesgue_measure (atom'' n) := tsum_fintype _
      _ = ∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then atomMeas n else 0 := by
          congr 1; funext n; simp only [atom'']
          by_cases h : atomMembership k k' n (k + i)
          · simp only [h, ite_true]; rfl
          · simp only [h]; exact Lebesgue_measure.empty

  -- Step 7: Compute weightedMeasureSum using decomposition
  calc weightedMeasureSum c E
      = ∑ i : Fin k, (c i) * Lebesgue_measure (E i) := rfl
    _ = ∑ i : Fin k, (c i) * (∑ n : Fin (2^(k+k')), if atomMembership k k' n i then atomMeas n else 0) := by
        congr 1; ext i; congr 1; exact hmes_decomp i
    _ = ∑ i : Fin k, ∑ n : Fin (2^(k+k')), (c i) * (if atomMembership k k' n i then atomMeas n else 0) := by
        congr 1; ext i
        -- c i * sum = sum of c i * each term
        have hf_nonneg : ∀ n : Fin (2^(k+k')), 0 ≤ (if atomMembership k k' n i then atomMeas n else 0) := by
          intro n
          split_ifs
          · exact Lebesgue_outer_measure.nonneg _
          · rfl
        exact EReal.mul_finset_sum_of_nonneg (2^(k+k')) (c i) (fun n => if atomMembership k k' n i then atomMeas n else 0) hf_nonneg
    _ = ∑ i : Fin k, ∑ n : Fin (2^(k+k')), if atomMembership k k' n i then (c i) * atomMeas n else 0 := by
        congr 1; ext i; congr 1; ext n
        split_ifs <;> simp
    _ = ∑ n : Fin (2^(k+k')), ∑ i : Fin k, if atomMembership k k' n i then (c i) * atomMeas n else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ n : Fin (2^(k+k')), atomMeas n * (∑ i : Fin k, if atomMembership k k' n i then c i else 0) := by
        congr 1; ext n
        -- Factoring: ∑ i, if p then c i * m else 0 = m * ∑ i, if p then c i else 0
        have hc_nonneg : ∀ i : Fin k, 0 ≤ (if atomMembership k k' n i then c i else 0) := fun i => by
          split_ifs; exact hnonneg i; rfl
        rw [EReal.mul_finset_sum_of_nonneg k (atomMeas n) _ hc_nonneg]
        congr 1; ext i
        split_ifs with h
        · -- c i * atomMeas n = atomMeas n * c i
          exact (EReal.mul_comm (atomMeas n) (c i)).symm
        · simp
    _ = ∑ n : Fin (2^(k+k')), atomMeas n * (∑ i : Fin k', if atomMembership k k' n (k + i) then c' i else 0) := by
        congr 1; ext n
        by_cases h : (atom E E' n).Nonempty
        · congr 1; exact hbit_eq n h
        · -- Empty atom has measure 0, so this term is 0
          rw [Set.not_nonempty_iff_eq_empty] at h
          have hzero : atomMeas n = 0 := by
            simp only [atomMeas, h, Lebesgue_measure.empty]
          simp only [hzero, zero_mul]
    _ = ∑ n : Fin (2^(k+k')), ∑ i : Fin k', if atomMembership k k' n (k + i) then (c' i) * atomMeas n else 0 := by
        congr 1; ext n
        -- Expanding: m * ∑ i, if p then c i else 0 = ∑ i, if p then c i * m else 0
        have hc'_nonneg : ∀ i : Fin k', 0 ≤ (if atomMembership k k' n (k + i) then c' i else 0) := fun i => by
          split_ifs; exact hnonneg' i; rfl
        rw [EReal.mul_finset_sum_of_nonneg k' (atomMeas n) _ hc'_nonneg]
        congr 1; ext i
        split_ifs with h
        · exact EReal.mul_comm (atomMeas n) (c' i)
        · simp
    _ = ∑ i : Fin k', ∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then (c' i) * atomMeas n else 0 := by
        rw [Finset.sum_comm]
    _ = ∑ i : Fin k', (c' i) * (∑ n : Fin (2^(k+k')), if atomMembership k k' n (k + i) then atomMeas n else 0) := by
        congr 1; ext i
        -- c' i * sum = sum of c' i * each term, then distribute through conditionals
        have hf_nonneg : ∀ n : Fin (2^(k+k')), 0 ≤ (if atomMembership k k' n (k + i) then atomMeas n else 0) := by
          intro n
          split_ifs
          · exact Lebesgue_outer_measure.nonneg _
          · rfl
        rw [EReal.mul_finset_sum_of_nonneg (2^(k+k')) (c' i) _ hf_nonneg]
        congr 1; ext n
        split_ifs <;> simp
    _ = ∑ i : Fin k', (c' i) * Lebesgue_measure (E' i) := by
        congr 1; ext i; congr 1; exact (hmes_decomp' i).symm
    _ = weightedMeasureSum c' E' := rfl

/-! ## Single-family atoms (k' = 0 specialization)

When working with a single family of sets (no second family to compare against),
we specialize the atom machinery with k' = 0. -/

/-- The atom for a single family of sets, using k' = 0 in the general atom definition -/
def singleAtom {X : Type*} {k : ℕ} (E : Fin k → Set X) (n : Fin (2^k)) : Set X :=
  atom E (fun _ : Fin 0 => ∅) ⟨n.val, by simp only [add_zero]; exact n.isLt⟩

/-- Single atoms are pairwise disjoint -/
lemma singleAtom_pairwiseDisjoint {X : Type*} {k : ℕ} (E : Fin k → Set X) :
    Set.univ.PairwiseDisjoint (singleAtom E) := by
  intro i _ j _ hij
  simp only [Function.onFun, singleAtom]
  have hlt_i : i.val < 2^(k+0) := by simp only [add_zero]; exact i.isLt
  have hlt_j : j.val < 2^(k+0) := by simp only [add_zero]; exact j.isLt
  have hij' : (⟨i.val, hlt_i⟩ : Fin (2^(k+0))) ≠ ⟨j.val, hlt_j⟩ := by
    intro h; apply hij; ext; exact Fin.mk.inj h
  exact atom_pairwiseDisjoint E (fun _ : Fin 0 => ∅) (by simp : i ∈ Set.univ) (by simp : j ∈ Set.univ) hij'

/-- Membership in singleAtom is determined by bit pattern -/
lemma mem_singleAtom_iff {X : Type*} {k : ℕ} (E : Fin k → Set X) (n : Fin (2^k)) (x : X) :
    x ∈ singleAtom E n ↔ ∀ i : Fin k, n.val.testBit i.val ↔ x ∈ E i := by
  simp only [singleAtom, atom, Set.mem_setOf_eq]
  constructor
  · intro ⟨h1, _⟩ i
    specialize h1 i
    rw [atomMembership_eq_testBit] at h1
    convert h1 using 1
  · intro h
    constructor
    · intro i
      rw [atomMembership_eq_testBit]
      exact h i
    · intro i; exact Fin.elim0 i

/-- Every point is in exactly one singleAtom -/
lemma exists_unique_singleAtom {X : Type*} [DecidableEq X] {k : ℕ} (E : Fin k → Set X) (x : X) :
    ∃! n : Fin (2^k), x ∈ singleAtom E n := by
  let n : ℕ := atomIndexOf E (fun _ : Fin 0 => ∅) x
  have hn_lt : n < 2^k := by
    have := atomIndexOf_lt E (fun _ : Fin 0 => ∅) x
    simp only [add_zero] at this
    exact this
  use ⟨n, hn_lt⟩
  constructor
  · simp only
    rw [mem_singleAtom_iff]
    intro i
    exact atomIndexOf_testBit_E E (fun _ : Fin 0 => ∅) x i
  · intro m hm
    ext
    rw [mem_singleAtom_iff] at hm
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < k
    · have h1 := hm ⟨j, hj⟩
      have h2 := atomIndexOf_testBit_E E (fun _ : Fin 0 => ∅) x ⟨j, hj⟩
      by_cases hx : x ∈ E ⟨j, hj⟩
      · rw [h1.mpr hx, h2.mpr hx]
      · have hm_false : (m.val.testBit j) = false := Bool.eq_false_iff.mpr (fun ht => hx (h1.mp ht))
        have hn_false : (n.testBit j) = false := Bool.eq_false_iff.mpr (fun ht => hx (h2.mp ht))
        rw [hm_false, hn_false]
    · have hm_lt : m.val < 2^k := m.isLt
      have hn_lt' : (atomIndexOf E (fun _ : Fin 0 => ∅) x) < 2^k := hn_lt
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm_lt (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (le_of_not_gt hj)))]
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hn_lt' (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (le_of_not_gt hj)))]

/-- The value on atom n is the sum of coefficients for sets containing that atom -/
noncomputable def atomValue {k : ℕ} (c : Fin k → ℝ) (n : Fin (2^k)) : ℝ :=
  ∑ i : Fin k, if n.val.testBit i.val then c i else 0

end UnsignedSimpleFunction.IntegralWellDef

/-- Lemma 1.3.4 (Well-definedness of simple integral) -/
lemma UnsignedSimpleFunction.integral_eq {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) {k:ℕ} {c: Fin k → EReal}
    {E: Fin k → Set (EuclideanSpace' d)} (hmes: ∀ i, LebesgueMeasurable (E i)) (hnonneg: ∀ i, c i ≥ 0)
    (heq: f = ∑ i, (c i) • (EReal.indicator (E i))) :
    hf.integ = ∑ i, (c i) * Lebesgue_measure (E i) := by
  -- Extract the canonical representation from hf
  -- hf gives: ∃ k', ∃ (c': Fin k' → EReal) (E': Fin k' → Set _), (∀ i, LebesgueMeasurable (E' i) ∧ c' i ≥ 0) ∧ f = ∑...
  -- hf.choose_spec.choose is c', hf.choose_spec.choose_spec.choose is E'
  let k' := hf.choose
  let c' := hf.choose_spec.choose
  let E' := hf.choose_spec.choose_spec.choose
  have hmes'_nonneg : ∀ i, LebesgueMeasurable (E' i) ∧ c' i ≥ 0 := hf.choose_spec.choose_spec.choose_spec.1
  have heq' : f = ∑ i, (c' i) • (EReal.indicator (E' i)) := hf.choose_spec.choose_spec.choose_spec.2

  -- The canonical representation also equals f
  have hfunc_eq : ∑ i, (c i) • (EReal.indicator (E i)) = ∑ i, (c' i) • (EReal.indicator (E' i)) := by
    rw [← heq, ← heq']

  -- Apply the core lemma: two representations of the same function give the same weighted measure
  have h := IntegralWellDef.weightedMeasureSum_eq_of_eq
    hmes (fun i => (hmes'_nonneg i).1) hnonneg (fun i => (hmes'_nonneg i).2) hfunc_eq

  -- h says: weightedMeasureSum c E = weightedMeasureSum c' E'
  -- Goal: ∑ i, (c' i) * Lebesgue_measure (E' i) = ∑ i, (c i) * Lebesgue_measure (E i)
  simp only [UnsignedSimpleFunction.IntegralWellDef.weightedMeasureSum] at h
  exact h.symm

/-- Definition 1.3.5 (almost always) -/
def AlmostAlways {d:ℕ} (P: EuclideanSpace' d → Prop) : Prop :=
  IsNull { x | ¬ P x }

/-- Definition 1.3.5 (almost everywhere equal) -/
def AlmostEverywhereEqual {d:ℕ} {X: Type*} (f g: EuclideanSpace' d → X) : Prop :=
  AlmostAlways (fun x ↦ f x = g x)

/-- Definition 1.3.5 (support) -/
def Support {X Y: Type*} [Zero Y] (f: X → Y) : Set X := { x | f x ≠ 0 }

lemma UnsignedSimpleFunction.support_measurable {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) : LebesgueMeasurable (Support f) := by
  -- Extract the representation: f = ∑ i, c(i) • EReal.indicator(E_i)
  obtain ⟨k, c, E, hmes_nonneg, heq⟩ := hf
  -- Define E' i = E i if c i > 0, else ∅
  let E' : Fin k → Set (EuclideanSpace' d) := fun i => if c i > 0 then E i else ∅
  -- Each E' i is measurable
  have hE'_meas : ∀ i, LebesgueMeasurable (E' i) := fun i => by
    simp only [E']
    split_ifs with h
    · exact (hmes_nonneg i).1
    · exact LebesgueMeasurable.empty
  -- Key: Support f = ⋃ i, E' i
  have h_eq : Support f = ⋃ i, E' i := by
    ext x
    simp only [Support, Set.mem_setOf_eq, Set.mem_iUnion, E']
    constructor
    · -- (⊆) If f(x) ≠ 0, some c_i > 0 and x ∈ E_i
      intro hne
      rw [heq] at hne
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hne
      -- Sum of nonneg terms is nonzero, so some term is nonzero
      have h_exists := Finset.exists_ne_zero_of_sum_ne_zero hne
      obtain ⟨i, _, hi_ne⟩ := h_exists
      use i
      -- c i * indicator ≠ 0 means c i > 0 and x ∈ E i
      by_cases hc : c i > 0
      · simp only [hc, ↓reduceIte]
        by_cases hx : x ∈ E i
        · exact hx
        · -- If x ∉ E i, then indicator is 0, so c i * 0 = 0, contradiction
          simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem hx,
                     EReal.coe_zero, mul_zero] at hi_ne
          exact absurd rfl hi_ne
      · -- c i ≤ 0, but c i ≥ 0, so c i = 0
        have hc_zero : c i = 0 := le_antisymm (le_of_not_gt hc) (hmes_nonneg i).2
        simp only [hc_zero, zero_mul] at hi_ne
        exact absurd rfl hi_ne
    · -- (⊇) If x ∈ E' i for some i, then f(x) ≠ 0
      intro ⟨i, hi⟩
      split_ifs at hi with hc
      · -- c i > 0 and x ∈ E i
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        -- f(x) ≥ c i * indicator(E i)(x) = c i > 0
        have h_term_pos : c i * EReal.indicator (E i) x > 0 := by
          simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hi,
                     EReal.coe_one, mul_one]
          exact hc
        -- Sum of nonneg terms with one positive term is positive
        have h_sum_nonneg : ∀ j, 0 ≤ c j * EReal.indicator (E j) x := fun j =>
          mul_nonneg (hmes_nonneg j).2 (EReal.indicator_nonneg' (E j) x)
        have h_sum_pos : 0 < ∑ j : Fin k, c j * EReal.indicator (E j) x := by
          calc 0 < c i * EReal.indicator (E i) x := h_term_pos
            _ ≤ ∑ j : Fin k, c j * EReal.indicator (E j) x :=
                Finset.single_le_sum (fun j _ => h_sum_nonneg j) (Finset.mem_univ i)
        exact ne_of_gt h_sum_pos
      · -- hi : x ∈ ∅, contradiction
        exact absurd hi (Set.notMem_empty x)
  rw [h_eq]
  exact LebesgueMeasurable.finite_union hE'_meas

lemma AlmostAlways.ofAlways {d:ℕ} {P: EuclideanSpace' d → Prop} (h: ∀ x, P x) : AlmostAlways P := by
  -- AlmostAlways P means IsNull { x | ¬ P x }, i.e., Lebesgue_outer_measure { x | ¬ P x } = 0
  -- If ∀ x, P x, then { x | ¬ P x } = ∅
  unfold AlmostAlways IsNull
  have h_empty : { x | ¬ P x } = ∅ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact h x
  rw [h_empty]
  exact Lebesgue_outer_measure.of_empty d

lemma AlmostAlways.mp {d:ℕ} {P Q: EuclideanSpace' d → Prop} (hP: AlmostAlways P) (himp: ∀ x, P x → Q x) : AlmostAlways Q := by
  -- AlmostAlways P means IsNull { x | ¬ P x }, i.e., Lebesgue_outer_measure { x | ¬ P x } = 0
  -- If P → Q everywhere, then ¬Q → ¬P (contrapositive), so { x | ¬ Q x } ⊆ { x | ¬ P x }
  unfold AlmostAlways IsNull at *
  -- hP : Lebesgue_outer_measure { x | ¬ P x } = 0
  -- Goal: Lebesgue_outer_measure { x | ¬ Q x } = 0
  have h_subset : { x | ¬ Q x } ⊆ { x | ¬ P x } := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    exact fun hp => hx (himp x hp)
  -- By monotonicity: measure { x | ¬ Q x } ≤ measure { x | ¬ P x } = 0
  have h_le := Lebesgue_outer_measure.mono h_subset
  rw [hP] at h_le
  exact le_antisymm h_le (Lebesgue_outer_measure.nonneg _)

lemma AlmostAlways.countable {d:ℕ} {I: Type*} [Countable I] {P: I → EuclideanSpace' d → Prop} (hP: ∀ i, AlmostAlways (P i)) : AlmostAlways (fun x ↦ ∀ i, P i x) := by
  -- AlmostAlways (fun x ↦ ∀ i, P i x) means IsNull { x | ¬ ∀ i, P i x }
  -- { x | ¬ ∀ i, P i x } = { x | ∃ i, ¬ P i x } = ⋃ᵢ { x | ¬ P i x }
  -- Each { x | ¬ P i x } is null by hP, and a countable union of null sets is null
  unfold AlmostAlways IsNull at *
  -- Goal: Lebesgue_outer_measure { x | ¬ ∀ i, P i x } = 0
  -- hP i : Lebesgue_outer_measure { x | ¬ P i x } = 0
  have h_eq : { x | ¬ ∀ i, P i x } = ⋃ i, { x | ¬ P i x } := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, not_forall]
  rw [h_eq]
  -- Need: Lebesgue_outer_measure (⋃ i, { x | ¬ P i x }) = 0
  -- Use countable type I via Encodable
  cases nonempty_encodable I with
  | intro enc =>
    -- Now have Encodable I, can use ℕ-indexed union
    -- Reindex via Encodable.encode
    let E' : ℕ → Set (EuclideanSpace' d) := fun n => match @Encodable.decode I enc n with
      | some i => { x | ¬ P i x }
      | none => ∅
    have h_subset : (⋃ i : I, { x | ¬ P i x }) ⊆ ⋃ n : ℕ, E' n := by
      intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨i, hi⟩ := hx
      use @Encodable.encode I enc i
      simp only [E', @Encodable.encodek I enc]
      exact hi
    have h_le := Lebesgue_outer_measure.mono h_subset
    have h_E'_null : ∀ n, Lebesgue_outer_measure (E' n) = 0 := fun n => by
      simp only [E']
      cases h : @Encodable.decode I enc n with
      | none => exact Lebesgue_outer_measure.of_empty d
      | some i => exact hP i
    -- By countable subadditivity: m(⋃ E'_n) ≤ ∑' n, m(E'_n) = ∑' n, 0 = 0
    have h_sum_zero : ∑' n, Lebesgue_outer_measure (E' n) = 0 := by
      simp only [h_E'_null, tsum_zero]
    have h_union_le := Lebesgue_outer_measure.union_le E'
    have h_bound : Lebesgue_outer_measure (⋃ i : I, { x | ¬ P i x }) ≤ 0 :=
      calc Lebesgue_outer_measure (⋃ i : I, { x | ¬ P i x })
          ≤ Lebesgue_outer_measure (⋃ n, E' n) := h_le
        _ ≤ ∑' n, Lebesgue_outer_measure (E' n) := h_union_le
        _ = 0 := h_sum_zero
    exact le_antisymm h_bound (Lebesgue_outer_measure.nonneg _)

/-- Almost everywhere equality is reflexive -/
lemma AlmostEverywhereEqual.refl {d:ℕ} {X: Type*} (f: EuclideanSpace' d → X) :
    AlmostEverywhereEqual f f :=
  -- {x | f x ≠ f x} = ∅, which is null
  AlmostAlways.ofAlways (fun _ => rfl)

/-- Almost everywhere equality is symmetric -/
lemma AlmostEverywhereEqual.symm {d:ℕ} {X: Type*} {f g: EuclideanSpace' d → X}
    (h: AlmostEverywhereEqual f g) : AlmostEverywhereEqual g f := by
  -- {x | g x ≠ f x} = {x | f x ≠ g x}, same set
  unfold AlmostEverywhereEqual AlmostAlways IsNull at *
  convert h using 2
  ext x
  exact ne_comm

/-- Almost everywhere equality is transitive -/
lemma AlmostEverywhereEqual.trans {d:ℕ} {X: Type*} {f g h: EuclideanSpace' d → X}
    (hfg: AlmostEverywhereEqual f g) (hgh: AlmostEverywhereEqual g h) :
    AlmostEverywhereEqual f h := by
  -- {x | f x ≠ h x} ⊆ {x | f x ≠ g x} ∪ {x | g x ≠ h x}
  -- Union of two null sets is null
  unfold AlmostEverywhereEqual AlmostAlways IsNull at *
  have h_subset : {x | f x ≠ h x} ⊆ {x | f x ≠ g x} ∪ {x | g x ≠ h x} := by
    intro x hx
    simp only [Set.mem_setOf_eq, Set.mem_union] at *
    by_contra hc
    push_neg at hc
    exact hx (hc.1.trans hc.2)
  -- Express union as ℕ-indexed union for countable subadditivity
  let E : ℕ → Set (EuclideanSpace' d) := fun n =>
    match n with
    | 0 => {x | f x ≠ g x}
    | 1 => {x | g x ≠ h x}
    | _ => ∅
  have h_union_eq : {x | f x ≠ g x} ∪ {x | g x ≠ h x} = ⋃ n, E n := by
    ext x
    simp only [Set.mem_union, Set.mem_iUnion, E]
    constructor
    · intro hx
      cases hx with
      | inl hl => exact ⟨0, hl⟩
      | inr hr => exact ⟨1, hr⟩
    · intro ⟨n, hn⟩
      match n with
      | 0 => exact Or.inl hn
      | 1 => exact Or.inr hn
      | n + 2 => exact absurd hn (Set.notMem_empty x)
  have h_E_null : ∀ n, Lebesgue_outer_measure (E n) = 0 := fun n => by
    match n with
    | 0 => exact hfg
    | 1 => exact hgh
    | n + 2 => exact Lebesgue_outer_measure.of_empty d
  have h_sum_zero : ∑' n, Lebesgue_outer_measure (E n) = 0 := by simp only [h_E_null, tsum_zero]
  have h_union_le := Lebesgue_outer_measure.union_le E
  have h_bound : Lebesgue_outer_measure {x | f x ≠ h x} ≤ 0 :=
    calc Lebesgue_outer_measure {x | f x ≠ h x}
        ≤ Lebesgue_outer_measure (⋃ n, E n) := by rw [← h_union_eq]; exact Lebesgue_outer_measure.mono h_subset
      _ ≤ ∑' n, Lebesgue_outer_measure (E n) := h_union_le
      _ = 0 := h_sum_zero
  exact le_antisymm h_bound (Lebesgue_outer_measure.nonneg _)

/-- Almost everywhere equality is an equivalence relation -/
theorem AlmostEverywhereEqual.equivalence {d:ℕ} {X: Type*} :
    Equivalence (@AlmostEverywhereEqual d X) :=
  ⟨refl, symm, trans⟩

/-- Exercise 1.3.1 (i) (Unsigned linearity, sum) -/
lemma UnsignedSimpleFunction.integral_add {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g) :
  (hf.add hg).integ = hf.integ + hg.integ := by
  let k₁ := hf.choose
  let c₁ := hf.choose_spec.choose
  let E₁ := hf.choose_spec.choose_spec.choose
  have hmes₁ : ∀ i, LebesgueMeasurable (E₁ i) ∧ c₁ i ≥ 0 := hf.choose_spec.choose_spec.choose_spec.1
  have heq₁ : f = ∑ i, (c₁ i) • (EReal.indicator (E₁ i)) := hf.choose_spec.choose_spec.choose_spec.2
  let k₂ := hg.choose
  let c₂ := hg.choose_spec.choose
  let E₂ := hg.choose_spec.choose_spec.choose
  have hmes₂ : ∀ i, LebesgueMeasurable (E₂ i) ∧ c₂ i ≥ 0 := hg.choose_spec.choose_spec.choose_spec.1
  have heq₂ : g = ∑ i, (c₂ i) • (EReal.indicator (E₂ i)) := hg.choose_spec.choose_spec.choose_spec.2
  let cadd : Fin (k₁+k₂) → EReal := fun i => if h : i < k₁ then c₁ ⟨i, h⟩ else c₂ ⟨i - k₁, by omega⟩
  let Eadd : Fin (k₁+k₂) → Set (EuclideanSpace' d) := fun i => if h : i < k₁ then E₁ ⟨i, h⟩ else E₂ ⟨i - k₁, by omega⟩
  have hmes_add : ∀ i, LebesgueMeasurable (Eadd i) := by
    intro i
    simp only [Eadd]
    split_ifs with h <;> [exact (hmes₁ ⟨i, h⟩).1; exact (hmes₂ ⟨i - k₁, by omega⟩).1]
  have hnonneg_add : ∀ i, (cadd i) ≥ 0 := by
    intro i
    simp only [cadd]
    split_ifs with h <;> [exact (hmes₁ ⟨i, h⟩).2; exact (hmes₂ ⟨i - k₁, by omega⟩).2]
  have heq_add : f + g = ∑ i, (cadd i) • (EReal.indicator (Eadd i)) := by
    rw [heq₁, heq₂]
    ext x
    simp [cadd, Eadd, Fin.sum_univ_add]
    rfl
  have h1 : hf.integ = ∑ i : Fin k₁, (c₁ i) * Lebesgue_measure (E₁ i) := by
    rw [UnsignedSimpleFunction.integral_eq hf (hmes := fun i => (hmes₁ i).1) (hnonneg := fun i => (hmes₁ i).2) (heq := heq₁)]
  have h2 : hg.integ = ∑ i : Fin k₂, (c₂ i) * Lebesgue_measure (E₂ i) := by
    rw [UnsignedSimpleFunction.integral_eq hg (hmes := fun i => (hmes₂ i).1) (hnonneg := fun i => (hmes₂ i).2) (heq := heq₂)]
  have h3 : (hf.add hg).integ = ∑ i : Fin (k₁+k₂), (cadd i) * Lebesgue_measure (Eadd i) := by
    rw [UnsignedSimpleFunction.integral_eq (hf.add hg) (hmes := hmes_add) (hnonneg := hnonneg_add) (heq := heq_add)]
  rw [h1, h2, h3]
  rw [Fin.sum_univ_add]
  simp [cadd, Eadd]

/-- Exercise 1.3.1 (i) (Unsigned linearity, scalar multiple) -/
lemma UnsignedSimpleFunction.integral_smul {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) {c:EReal} (hc: c ≥ 0) :
  (hf.smul hc).integ = c * hf.integ := by
  let k := hf.choose
  let c₁ := hf.choose_spec.choose
  let E₁ := hf.choose_spec.choose_spec.choose
  have hmes₁ : ∀ i, LebesgueMeasurable (E₁ i) ∧ c₁ i ≥ 0 := hf.choose_spec.choose_spec.choose_spec.1
  have heq₁ : f = ∑ i, (c₁ i) • (EReal.indicator (E₁ i)) := hf.choose_spec.choose_spec.choose_spec.2
  have heq_smul : c • f = ∑ i, (c * c₁ i) • (EReal.indicator (E₁ i)) := by
    simp only [heq₁]
    ext x
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    rw [EReal.mul_finset_sum_of_nonneg k c (fun i => (c₁ i) * EReal.indicator (E₁ i) x)
        (fun i => mul_nonneg (hmes₁ i).2 (EReal.indicator_nonneg' (E₁ i) x))]
    congr 1
    ext i
    rw [mul_assoc]
  have h1 : (hf.smul hc).integ = ∑ i : Fin k, (c * c₁ i) * Lebesgue_measure (E₁ i) := by
    rw [UnsignedSimpleFunction.integral_eq (hf.smul hc) (hmes := fun i => (hmes₁ i).1)
        (hnonneg := fun i => mul_nonneg hc (hmes₁ i).2) (heq := heq_smul)]
  have h2 : hf.integ = ∑ i : Fin k, (c₁ i) * Lebesgue_measure (E₁ i) := by
    rw [UnsignedSimpleFunction.integral_eq hf (hmes := fun i => (hmes₁ i).1)
        (hnonneg := fun i => (hmes₁ i).2) (heq := heq₁)]
  rw [h1, h2]
  rw [EReal.mul_finset_sum_of_nonneg k c (fun i => c₁ i * Lebesgue_measure (E₁ i))
      (fun i => mul_nonneg (hmes₁ i).2 (by simpa [Lebesgue_measure] using Lebesgue_outer_measure.nonneg (E₁ i)))]
  congr 1
  ext i
  rw [mul_assoc]

/-- Public version of the (private) indicator nonnegativity lemma. -/
lemma EReal.indicator_nonneg {X : Type*} (A : Set X) (x : X) : 0 ≤ EReal.indicator A x := by
  simp only [EReal.indicator, Real.EReal_fun]
  exact EReal.coe_nonneg.mpr (Set.indicator_nonneg (fun _ _ => zero_le_one) x)

/-- Finite sum of EReals each {lit}`< ⊤` is {lit}`< ⊤`. -/
lemma EReal_sum_lt_top_of_all {k : ℕ} (a : Fin k → EReal) (hlt : ∀ i, a i < ⊤) :
    (∑ i, a i) < ⊤ := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_castSucc]
      exact EReal.add_lt_top
        (lt_top_iff_ne_top.mp (ih (fun i => a (Fin.castSucc i)) (fun i => hlt (Fin.castSucc i))))
        (lt_top_iff_ne_top.mp (hlt (Fin.last k)))

/-- If a nonneg finite sum is {lit}`< ⊤` then every term is {lit}`< ⊤`. -/
lemma EReal_sum_lt_top_iff_all {k : ℕ} (a : Fin k → EReal) (ha_nonneg : ∀ i, 0 ≤ a i) :
    (∑ i, a i < ⊤) → ∀ i, a i < ⊤ := by
  intro hsum i
  by_contra h
  have htop_le : ⊤ ≤ a i := le_of_not_gt h
  have hle_sum : a i ≤ ∑ j, a j :=
    Finset.single_le_sum (fun j _ => ha_nonneg j) (Finset.mem_univ i)
  exact absurd hsum (not_lt_of_ge (le_trans htop_le hle_sum))

/-- For nonneg terms, a finite sum is {lit}`< ⊤` iff every term is {lit}`< ⊤`. -/
lemma EReal_finset_sum_lt_top {k : ℕ} (a : Fin k → EReal) (ha_nonneg : ∀ i, 0 ≤ a i) :
    (∑ i, a i < ⊤) ↔ ∀ i, a i < ⊤ :=
  ⟨EReal_sum_lt_top_iff_all a ha_nonneg, EReal_sum_lt_top_of_all a⟩

/-- Product of nonneg finite EReals is finite. -/
lemma EReal.mul_lt_top_of_nonneg {a b : EReal} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a < ⊤)
    (hb : b < ⊤) : a * b < ⊤ := by
  lift a to ℝ using ⟨ne_of_lt ha, ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero ha0)⟩
  lift b to ℝ using ⟨ne_of_lt hb, ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero hb0)⟩
  norm_cast
  exact EReal.coe_lt_top (a * b)

/-- A weighted indicator sum equals ⊤ at x iff some E i contains x with c i = ⊤. -/
lemma EReal_sum_indicator_eq_top_iff {d k : ℕ} {c : Fin k → EReal}
    {E : Fin k → Set (EuclideanSpace' d)} (hnonneg : ∀ i, 0 ≤ c i) {x : EuclideanSpace' d} :
    (∑ i, c i * EReal.indicator (E i) x = ⊤) ↔ ∃ i, x ∈ E i ∧ c i = ⊤ := by
  constructor
  · intro hx
    by_contra h
    push_neg at h
    have hterm_lt : ∀ i, c i * EReal.indicator (E i) x < ⊤ := fun i => by
      by_cases hxmem : x ∈ E i
      · rw [UnsignedSimpleFunction.IntegralWellDef.indicator_mul_mem (E i) (c i) x hxmem]
        exact lt_top_iff_ne_top.mpr (h i hxmem)
      · rw [UnsignedSimpleFunction.IntegralWellDef.indicator_mul_not_mem (E i) (c i) x hxmem]
        exact EReal.zero_lt_top
    have hsum_lt : (∑ i, c i * EReal.indicator (E i) x) < ⊤ :=
      EReal_sum_lt_top_of_all _ hterm_lt
    exact absurd hx (ne_of_lt hsum_lt)
  · rintro ⟨i, hxEi, hci⟩
    have hterm : c i * EReal.indicator (E i) x = ⊤ := by
      rw [UnsignedSimpleFunction.IntegralWellDef.indicator_mul_mem (E i) (c i) x hxEi, hci]
    have hle : c i * EReal.indicator (E i) x ≤ ∑ j, c j * EReal.indicator (E j) x :=
      Finset.single_le_sum (fun j _ => mul_nonneg (hnonneg j) (EReal.indicator_nonneg (E j) x))
        (Finset.mem_univ i)
    exact le_antisymm le_top (hterm ▸ hle)

/-- A finite union of null sets is null. -/
lemma IsNull.finite_iUnion {d k : ℕ} {S : Fin k → Set (EuclideanSpace' d)} (hS : ∀ i, IsNull (S i)) :
    IsNull (⋃ i, S i) := by
  have hsum : (∑ i, Lebesgue_outer_measure (S i)) = 0 := by
    simp [hS]
  have hle := Lebesgue_outer_measure.finite_union_le S
  rw [hsum] at hle
  exact le_antisymm hle (Lebesgue_outer_measure.nonneg _)

/-- The support of a weighted indicator sum is the union of the E i with c i > 0. -/
lemma support_eq_iUnion_pos {d k : ℕ} {f : EuclideanSpace' d → EReal} (c : Fin k → EReal)
    (E : Fin k → Set (EuclideanSpace' d)) (hnonneg : ∀ i, 0 ≤ c i)
    (heq : f = ∑ i, (c i) • (EReal.indicator (E i))) :
    Support f = ⋃ i, (if c i > 0 then E i else ∅) := by
  ext x
  simp only [Support, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · intro hne
    rw [heq] at hne
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hne
    have h_exists := Finset.exists_ne_zero_of_sum_ne_zero hne
    obtain ⟨i, _, hi_ne⟩ := h_exists
    use i
    by_cases hc : c i > 0
    · simp only [hc, ↓reduceIte]
      by_cases hx : x ∈ E i
      · exact hx
      · simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem hx,
                   EReal.coe_zero, mul_zero] at hi_ne
        exact absurd rfl hi_ne
    · have hc_zero : c i = 0 := le_antisymm (le_of_not_gt hc) (hnonneg i)
      simp only [hc_zero, zero_mul] at hi_ne
      exact absurd rfl hi_ne
  · intro ⟨i, hi⟩
    split_ifs at hi with hc
    · rw [heq]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have h_term_pos : c i * EReal.indicator (E i) x > 0 := by
        simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hi,
                   EReal.coe_one, mul_one]
        exact hc
      have h_sum_nonneg : ∀ j, 0 ≤ c j * EReal.indicator (E j) x := fun j =>
        mul_nonneg (hnonneg j) (EReal.indicator_nonneg (E j) x)
      have h_sum_pos : 0 < ∑ j : Fin k, c j * EReal.indicator (E j) x := by
        calc 0 < c i * EReal.indicator (E i) x := h_term_pos
          _ ≤ ∑ j : Fin k, c j * EReal.indicator (E j) x :=
              Finset.single_le_sum (fun j _ => h_sum_nonneg j) (Finset.mem_univ i)
      exact ne_of_gt h_sum_pos
    · exact absurd hi (Set.notMem_empty x)

/-- Exercise 1.3.1 (ii) (Finiteness) -/
lemma UnsignedSimpleFunction.integral_finite_iff {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) :
  (hf.integ < ⊤) ↔ (AlmostAlways (fun x ↦ f x < ⊤)) ∧ (Lebesgue_measure (Support f)) < ⊤ := by
  have hf0 : UnsignedSimpleFunction f := hf
  obtain ⟨k, c, E, hmes_nonneg, heq⟩ := hf0
  have hmes : ∀ i, LebesgueMeasurable (E i) := fun i => (hmes_nonneg i).1
  have hnonneg : ∀ i, c i ≥ 0 := fun i => (hmes_nonneg i).2
  have hinteg : hf.integ = ∑ i, c i * Lebesgue_measure (E i) :=
    UnsignedSimpleFunction.integral_eq hf (hmes := hmes) (hnonneg := hnonneg) (heq := heq)
  rw [hinteg]
  constructor
  · intro hsum_lt
    have hprod_nonneg : ∀ i, 0 ≤ c i * Lebesgue_measure (E i) := fun i =>
      mul_nonneg (hnonneg i) (Lebesgue_outer_measure.nonneg (E i))
    have hterm_lt : ∀ i, c i * Lebesgue_measure (E i) < ⊤ :=
      EReal_sum_lt_top_iff_all _ hprod_nonneg hsum_lt
    have hpoint : ∀ x, f x = ⊤ → ∃ i, x ∈ E i ∧ c i = ⊤ := by
      intro x hx
      rw [heq] at hx
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hx
      exact (EReal_sum_indicator_eq_top_iff hnonneg).1 hx
    have hm_top_zero : ∀ i, c i = ⊤ → Lebesgue_measure (E i) = 0 := fun i hci => by
      by_contra hne
      have hpos : 0 < Lebesgue_measure (E i) :=
        lt_of_le_of_ne (Lebesgue_outer_measure.nonneg (E i)) (Ne.symm hne)
      have htop : ⊤ * Lebesgue_measure (E i) = ⊤ := EReal.top_mul_of_pos hpos
      have hlt : ⊤ * Lebesgue_measure (E i) < ⊤ := by simpa [hci] using hterm_lt i
      rw [htop] at hlt
      exact (lt_irrefl ⊤) hlt
    constructor
    · have hsub : {x | ¬ f x < ⊤} ⊆ ⋃ i, (if c i = ⊤ then E i else ∅) := by
        intro x hx
        simp only [Set.mem_setOf_eq] at hx
        have hxtop : f x = ⊤ := le_antisymm le_top (le_of_not_gt hx)
        obtain ⟨i, hxEi, hci⟩ := hpoint x hxtop
        exact Set.mem_iUnion.mpr ⟨i, by simp [hci, hxEi]⟩
      have hnull_union : IsNull (⋃ i, (if c i = ⊤ then E i else ∅)) := by
        apply IsNull.finite_iUnion
        intro i
        by_cases hci : c i = ⊤
        · simpa [hci] using hm_top_zero i hci
        · simpa [hci] using (Lebesgue_outer_measure.of_empty d : IsNull (∅ : Set (EuclideanSpace' d)))
      exact IsNull.subset hnull_union hsub
    · have hsup_eq : Support f = ⋃ i, (if c i > 0 then E i else ∅) :=
        support_eq_iUnion_pos c E hnonneg heq
      rw [hsup_eq]
      have hle := Lebesgue_outer_measure.finite_union_le (fun i : Fin k => if c i > 0 then E i else ∅)
      have hterm_fin : ∀ i, Lebesgue_measure (if c i > 0 then E i else ∅) < ⊤ := fun i => by
        by_cases hci : c i > 0
        · have hmi : Lebesgue_measure (E i) < ⊤ := by
            by_contra hne
            have htop : Lebesgue_measure (E i) = ⊤ := le_antisymm le_top (le_of_not_gt hne)
            have hlt : c i * Lebesgue_measure (E i) < ⊤ := hterm_lt i
            have hmul : c i * Lebesgue_measure (E i) = ⊤ := by
              rw [htop]
              exact EReal.mul_top_of_pos hci
            rw [hmul] at hlt
            exact (lt_irrefl ⊤) hlt
          simp [hci]
          exact hmi
        · have hci0 : c i = 0 := le_antisymm (le_of_not_gt hci) (hnonneg i)
          simp [hci0]
      have hsum_fin : (∑ i, Lebesgue_measure (if c i > 0 then E i else ∅)) < ⊤ :=
        EReal_sum_lt_top_of_all _ hterm_fin
      exact lt_of_le_of_lt hle hsum_fin
  · intro h
    rcases h with ⟨haa, hmsup⟩
    have hterm_lt : ∀ i, c i * Lebesgue_measure (E i) < ⊤ := fun i => by
      by_cases hci : c i = ⊤
      · have hsub : E i ⊆ {x | ¬ f x < ⊤} := by
          intro x hx
          simp only [Set.mem_setOf_eq]
          intro hlt
          have hxeq : f x = ⊤ := by
            rw [heq]
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
            exact (EReal_sum_indicator_eq_top_iff hnonneg).2 ⟨i, hx, hci⟩
          exact (lt_irrefl ⊤) (hxeq ▸ hlt)
        have hmi0 : Lebesgue_measure (E i) = 0 := IsNull.subset haa hsub
        have hmul0 : ⊤ * Lebesgue_measure (E i) = 0 := by
          rw [hmi0]
          exact mul_zero ⊤
        rw [hci, hmul0]
        exact EReal.zero_lt_top
      · have hci_lt : c i < ⊤ := lt_top_iff_ne_top.mpr hci
        by_cases hci0 : c i = 0
        · rw [hci0, zero_mul]
          exact EReal.zero_lt_top
        · have hci_pos : 0 < c i := lt_of_le_of_ne (hnonneg i) (Ne.symm hci0)
          have hmi_lt : Lebesgue_measure (E i) < ⊤ := by
            have hsub : E i ⊆ Support f := by
              rw [support_eq_iUnion_pos c E hnonneg heq]
              intro x hx
              exact Set.mem_iUnion.mpr ⟨i, by simp [hci_pos, hx]⟩
            exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hmsup
          exact EReal.mul_lt_top_of_nonneg (hnonneg i) (Lebesgue_outer_measure.nonneg (E i))
            hci_lt hmi_lt
    exact EReal_sum_lt_top_of_all _ hterm_lt

/-- A finite sum of nonnegative EReals is zero iff every term is zero (the forward
direction we need here). -/
private lemma sum_eq_zero_of_nonneg {k : ℕ} {a : Fin k → EReal} (ha : ∀ i, 0 ≤ a i)
    (hsum : (∑ i, a i) = 0) : ∀ i, a i = 0 := by
  intro i
  by_contra hne
  have hpos : 0 < a i := lt_of_le_of_ne (ha i) (Ne.symm hne)
  have hle : a i ≤ ∑ i, a i :=
    Finset.single_le_sum (fun j _ => ha j) (Finset.mem_univ i)
  have hsum_pos : 0 < ∑ i, a i := lt_of_lt_of_le hpos hle
  exact absurd hsum (ne_of_gt hsum_pos)

/-- If a positive EReal times a nonnegative EReal is zero, the second factor is zero. -/
private lemma mul_eq_zero_of_pos_left {a b : EReal} (ha : 0 < a) (hb0 : 0 ≤ b)
    (hprod : a * b = 0) : b = 0 := by
  by_contra hne
  have hbpos : 0 < b := lt_of_le_of_ne hb0 (Ne.symm hne)
  have hprod_pos : 0 < a * b := EReal.mul_pos ha hbpos
  exact absurd hprod (ne_of_gt hprod_pos)

/-- Exercise 1.3.1 (iii) (Vanishing) -/
lemma UnsignedSimpleFunction.integral_eq_zero_iff {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) :
  (hf.integ = 0) ↔ AlmostAlways (fun x ↦ f x = 0) := by
  have hf0 : UnsignedSimpleFunction f := hf
  obtain ⟨k, c, E, hmes_nonneg, heq⟩ := hf0
  have hmes : ∀ i, LebesgueMeasurable (E i) := fun i => (hmes_nonneg i).1
  have hnonneg : ∀ i, c i ≥ 0 := fun i => (hmes_nonneg i).2
  have hinteg : hf.integ = ∑ i, c i * Lebesgue_measure (E i) :=
    UnsignedSimpleFunction.integral_eq hf (hmes := hmes) (hnonneg := hnonneg) (heq := heq)
  rw [hinteg]
  change (∑ i, c i * Lebesgue_measure (E i) = 0) ↔ IsNull (Support f)
  rw [support_eq_iUnion_pos c E hnonneg heq]
  constructor
  · intro hsum
    have hterm0 : ∀ i, c i * Lebesgue_measure (E i) = 0 :=
      sum_eq_zero_of_nonneg
        (fun i => mul_nonneg (hnonneg i) (Lebesgue_outer_measure.nonneg (E i))) hsum
    apply IsNull.finite_iUnion
    intro i
    by_cases hc : c i > 0
    · have hm0 : Lebesgue_measure (E i) = 0 :=
        mul_eq_zero_of_pos_left hc (Lebesgue_outer_measure.nonneg (E i)) (hterm0 i)
      simpa [hc, hm0]
    · simpa [hc] using (Lebesgue_outer_measure.of_empty d : IsNull (∅ : Set (EuclideanSpace' d)))
  · intro hnull
    have hterm0 : ∀ i, c i * Lebesgue_measure (E i) = 0 := by
      intro i
      by_cases hc : c i > 0
      · have hsub : E i ⊆ ⋃ j, (if c j > 0 then E j else ∅) := by
          intro x hx
          exact Set.mem_iUnion.mpr ⟨i, by simp [hc, hx]⟩
        have hEi_null : IsNull (E i) := IsNull.subset hnull hsub
        have hm0 : Lebesgue_measure (E i) = 0 := hEi_null
        rw [hm0, mul_zero]
      · have hci0 : c i = 0 := le_antisymm (le_of_not_gt hc) (hnonneg i)
        rw [hci0, zero_mul]
    simp [hterm0]

open UnsignedSimpleFunction.IntegralWellDef

/-- The value on a joint atom for EReal coefficients: sum over bits of the first k coordinates. -/
noncomputable def atomValueEReal {k : ℕ} (c : Fin k → EReal) (n : ℕ) : EReal :=
  ∑ i : Fin k, if n.testBit i.val then c i else 0

/-- The value on a joint atom for EReal coefficients: sum over bits of the last l coordinates. -/
noncomputable def atomValueERealShift {k l : ℕ} (c : Fin l → EReal) (n : Fin (2^(k+l))) : EReal :=
  ∑ j : Fin l, if n.val.testBit (k + j.val) then c j else 0

/-- atomValueEReal is nonnegative for nonnegative coefficients. -/
lemma atomValueEReal_nonneg {k : ℕ} {c : Fin k → EReal} (hc : ∀ i, 0 ≤ c i) (n : ℕ) :
    0 ≤ atomValueEReal c n := by
  simp only [atomValueEReal]
  apply Finset.sum_nonneg
  intro i _
  by_cases h : n.testBit i.val
  · simp [h, hc i]
  · simp [h]

/-- atomValueERealShift is nonnegative for nonnegative coefficients. -/
lemma atomValueERealShift_nonneg {k l : ℕ} {c : Fin l → EReal} (hc : ∀ j, 0 ≤ c j)
    (n : Fin (2^(k+l))) : 0 ≤ atomValueERealShift c n := by
  simp only [atomValueERealShift]
  apply Finset.sum_nonneg
  intro j _
  by_cases h : n.val.testBit (k + j.val)
  · simp [h, hc j]
  · simp [h]

/-- On a point in the joint atom n, the E-sum equals atomValueEReal of the first k bits. -/
lemma sum_indicator_eq_atomValueEReal {d k l : ℕ} (c : Fin k → EReal)
    (E : Fin k → Set (EuclideanSpace' d)) (F : Fin l → Set (EuclideanSpace' d))
    (n : Fin (2^(k+l))) (x : EuclideanSpace' d) (hx : x ∈ atom E F n) :
    (∑ i : Fin k, (c i) * (EReal.indicator (E i) x)) = atomValueEReal c n.val := by
  simp only [atomValueEReal]
  apply Finset.sum_congr rfl
  intro i _
  have hbit_iff : n.val.testBit i.val ↔ x ∈ E i := by
    simpa [atomMembership_eq_testBit] using (hx.1 i)
  by_cases hbit : n.val.testBit i.val = true
  · have hx_in : x ∈ E i := hbit_iff.mp hbit
    simp [hbit, EReal.indicator_of_mem hx_in]
  · have hbit_false : n.val.testBit i.val = false := Bool.eq_false_iff.mpr hbit
    have hx_out : x ∉ E i := fun h => hbit (hbit_iff.mpr h)
    simp [hbit_false, EReal.indicator_of_notMem hx_out]

/-- On a point in the joint atom n, the E'-sum equals atomValueERealShift of the last l bits. -/
lemma sum_indicator_eq_atomValueERealShift {d k l : ℕ} (c : Fin l → EReal)
    (E : Fin k → Set (EuclideanSpace' d)) (F : Fin l → Set (EuclideanSpace' d))
    (n : Fin (2^(k+l))) (x : EuclideanSpace' d) (hx : x ∈ atom E F n) :
    (∑ j : Fin l, (c j) * (EReal.indicator (F j) x)) = atomValueERealShift c n := by
  simp only [atomValueERealShift]
  apply Finset.sum_congr rfl
  intro j _
  have hbit_iff : n.val.testBit (k + j.val) ↔ x ∈ F j := by
    simpa [atomMembership_eq_testBit] using (hx.2 j)
  by_cases hbit : n.val.testBit (k + j.val) = true
  · have hx_in : x ∈ F j := hbit_iff.mp hbit
    simp [hbit, EReal.indicator_of_mem hx_in]
  · have hbit_false : n.val.testBit (k + j.val) = false := Bool.eq_false_iff.mpr hbit
    have hx_out : x ∉ F j := fun h => hbit (hbit_iff.mpr h)
    simp [hbit_false, EReal.indicator_of_notMem hx_out]

/-- The E-sum equals the sum over joint atoms of atomValueEReal times the atom indicator. -/
lemma eq_sum_atomValueEReal_indicator {d k l : ℕ} (c : Fin k → EReal)
    (E : Fin k → Set (EuclideanSpace' d)) (F : Fin l → Set (EuclideanSpace' d)) :
    (∑ i : Fin k, (c i) • (EReal.indicator (E i))) =
      ∑ n : Fin (2^(k+l)), (atomValueEReal c n.val) • (EReal.indicator (atom E F n)) := by
  classical
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  let n0 : Fin (2^(k+l)) := ⟨atomIndexOf E F x, atomIndexOf_lt E F x⟩
  have hx_mem : x ∈ atom E F n0 := by
    simp only [atom, Set.mem_setOf_eq, n0]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E E F x j]
    · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E' E F x j]
  have hunique : ∀ m : Fin (2^(k+l)), x ∈ atom E F m → m = n0 := by
    intro m hm
    by_contra hne
    have hdisj : Disjoint (atom E F m) (atom E F n0) :=
      atom_pairwiseDisjoint E F (by simp) (by simp) hne
    exact (Set.disjoint_left.mp hdisj) hm hx_mem
  have hrhs : (∑ m : Fin (2^(k+l)), atomValueEReal c m.val * EReal.indicator (atom E F m) x) =
      atomValueEReal c n0.val := by
    rw [Finset.sum_eq_single n0]
    · simp only [EReal.indicator_of_mem hx_mem, mul_one]
    · intro m _ hm_ne
      have hx_notin : x ∉ atom E F m := fun h => hm_ne (hunique m h)
      simp only [EReal.indicator_of_notMem hx_notin, mul_zero]
    · intro h; exact absurd (Finset.mem_univ n0) h
  rw [hrhs]
  exact sum_indicator_eq_atomValueEReal c E F n0 x hx_mem

/-- The E'-sum equals the sum over joint atoms of atomValueERealShift times the atom indicator. -/
lemma eq_sum_atomValueERealShift_indicator {d k l : ℕ} (c : Fin l → EReal)
    (E : Fin k → Set (EuclideanSpace' d)) (F : Fin l → Set (EuclideanSpace' d)) :
    (∑ j : Fin l, (c j) • (EReal.indicator (F j))) =
      ∑ n : Fin (2^(k+l)), (atomValueERealShift c n) • (EReal.indicator (atom E F n)) := by
  classical
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  let n0 : Fin (2^(k+l)) := ⟨atomIndexOf E F x, atomIndexOf_lt E F x⟩
  have hx_mem : x ∈ atom E F n0 := by
    simp only [atom, Set.mem_setOf_eq, n0]
    refine ⟨fun j => ?_, fun j => ?_⟩
    · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E E F x j]
    · rw [atomMembership_eq_testBit, atomIndexOf_testBit_E' E F x j]
  have hunique : ∀ m : Fin (2^(k+l)), x ∈ atom E F m → m = n0 := by
    intro m hm
    by_contra hne
    have hdisj : Disjoint (atom E F m) (atom E F n0) :=
      atom_pairwiseDisjoint E F (by simp) (by simp) hne
    exact (Set.disjoint_left.mp hdisj) hm hx_mem
  have hrhs : (∑ m : Fin (2^(k+l)), atomValueERealShift c m * EReal.indicator (atom E F m) x) =
      atomValueERealShift c n0 := by
    rw [Finset.sum_eq_single n0]
    · simp only [EReal.indicator_of_mem hx_mem, mul_one]
    · intro m _ hm_ne
      have hx_notin : x ∉ atom E F m := fun h => hm_ne (hunique m h)
      simp only [EReal.indicator_of_notMem hx_notin, mul_zero]
    · intro h; exact absurd (Finset.mem_univ n0) h
  rw [hrhs]
  exact sum_indicator_eq_atomValueERealShift c E F n0 x hx_mem

/-- Exercise 1.3.1 (v) (Monotonicity) -/
lemma UnsignedSimpleFunction.integral_le_integral_of_aeLe {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g)
  (hae: AlmostAlways (fun x ↦ f x ≤ g x)) :
  hf.integ ≤ hg.integ := by
  let k₁ := hf.choose
  let c₁ := hf.choose_spec.choose
  let E₁ := hf.choose_spec.choose_spec.choose
  have hmes₁ : ∀ i, LebesgueMeasurable (E₁ i) ∧ c₁ i ≥ 0 := hf.choose_spec.choose_spec.choose_spec.1
  have heq₁ : f = ∑ i, (c₁ i) • (EReal.indicator (E₁ i)) := hf.choose_spec.choose_spec.choose_spec.2
  let k₂ := hg.choose
  let c₂ := hg.choose_spec.choose
  let E₂ := hg.choose_spec.choose_spec.choose
  have hmes₂ : ∀ i, LebesgueMeasurable (E₂ i) ∧ c₂ i ≥ 0 := hg.choose_spec.choose_spec.choose_spec.1
  have heq₂ : g = ∑ i, (c₂ i) • (EReal.indicator (E₂ i)) := hg.choose_spec.choose_spec.choose_spec.2
  let A : Fin (2^(k₁+k₂)) → Set (EuclideanSpace' d) := atom E₁ E₂
  have hA_mes : ∀ n, LebesgueMeasurable (A n) := by
    intro n
    simpa [A] using atom_measurable (fun i => (hmes₁ i).1) (fun j => (hmes₂ j).1) n
  have hf_eq_atoms : f = ∑ n : Fin (2^(k₁+k₂)), (atomValueEReal c₁ n.val) • (EReal.indicator (A n)) :=
    heq₁.trans (by simpa [A] using eq_sum_atomValueEReal_indicator c₁ E₁ E₂)
  have hg_eq_atoms : g = ∑ n : Fin (2^(k₁+k₂)), (atomValueERealShift c₂ n) • (EReal.indicator (A n)) :=
    heq₂.trans (by simpa [A] using eq_sum_atomValueERealShift_indicator c₂ E₁ E₂)
  have hf_integ : hf.integ = ∑ n : Fin (2^(k₁+k₂)), (atomValueEReal c₁ n.val) * Lebesgue_measure (A n) := by
    rw [UnsignedSimpleFunction.integral_eq hf (k := 2^(k₁+k₂))
      (c := fun n : Fin (2^(k₁+k₂)) => atomValueEReal c₁ n.val) (E := A)
      (hmes := hA_mes) (hnonneg := fun n => atomValueEReal_nonneg (fun i => (hmes₁ i).2) n.val)
      (heq := hf_eq_atoms)]
  have hg_integ : hg.integ = ∑ n : Fin (2^(k₁+k₂)), (atomValueERealShift c₂ n) * Lebesgue_measure (A n) := by
    rw [UnsignedSimpleFunction.integral_eq hg (k := 2^(k₁+k₂))
      (c := fun n : Fin (2^(k₁+k₂)) => atomValueERealShift c₂ n) (E := A)
      (hmes := hA_mes) (hnonneg := fun n => atomValueERealShift_nonneg (fun i => (hmes₂ i).2) n)
      (heq := hg_eq_atoms)]
  have hcmp : ∀ n : Fin (2^(k₁+k₂)),
      atomValueEReal c₁ n.val ≤ atomValueERealShift c₂ n ∨ Lebesgue_measure (A n) = 0 := by
    intro n
    by_cases hle : atomValueEReal c₁ n.val ≤ atomValueERealShift c₂ n
    · exact Or.inl hle
    · right
      have hgt : atomValueERealShift c₂ n < atomValueEReal c₁ n.val := lt_of_not_ge hle
      have hsub : A n ⊆ {x | ¬ f x ≤ g x} := by
        intro x hx
        have hfx : f x = atomValueEReal c₁ n.val := by
          exact (congrFun heq₁ x).trans (by
            simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
              using (sum_indicator_eq_atomValueEReal c₁ E₁ E₂ n x hx))
        have hgx : g x = atomValueERealShift c₂ n := by
          exact (congrFun heq₂ x).trans (by
            simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
              using (sum_indicator_eq_atomValueERealShift c₂ E₁ E₂ n x hx))
        change ¬ f x ≤ g x
        rw [hfx, hgx]
        exact not_le_of_gt hgt
      have hnull : IsNull (A n) := IsNull.subset hae hsub
      simpa [Lebesgue_measure] using hnull
  have hterm : ∀ n : Fin (2^(k₁+k₂)),
      (atomValueEReal c₁ n.val) * Lebesgue_measure (A n) ≤
        (atomValueERealShift c₂ n) * Lebesgue_measure (A n) := by
    intro n
    rcases hcmp n with hle | hzero
    · exact mul_le_mul_of_nonneg_right hle (Lebesgue_outer_measure.nonneg (A n))
    · rw [hzero]
      simp
  have hsum_le : (∑ n : Fin (2^(k₁+k₂)), (atomValueEReal c₁ n.val) * Lebesgue_measure (A n)) ≤
      (∑ n : Fin (2^(k₁+k₂)), (atomValueERealShift c₂ n) * Lebesgue_measure (A n)) :=
    Finset.sum_le_sum (fun n _ => hterm n)
  rw [hf_integ, hg_integ]
  exact hsum_le

/-- Exercise 1.3.1 (iv) (Equivalence) -/
lemma UnsignedSimpleFunction.integral_eq_integral_of_aeEqual {d:ℕ} {f g: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) (hg: UnsignedSimpleFunction g)
  (hae: AlmostEverywhereEqual f g) :
  hf.integ = hg.integ := by
  have h1 : hf.integ ≤ hg.integ := UnsignedSimpleFunction.integral_le_integral_of_aeLe hf hg (AlmostAlways.mp hae (fun x hx => le_of_eq hx))
  have h2 : hg.integ ≤ hf.integ := UnsignedSimpleFunction.integral_le_integral_of_aeLe hg hf (AlmostAlways.mp hae (fun x hx => le_of_eq hx.symm))
  exact le_antisymm h1 h2

/-- Exercise 1.3.1(vi) (Compatibility with Lebesgue measure, indicator) -/
lemma UnsignedSimpleFunction.indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  UnsignedSimpleFunction (Real.toEReal ∘ E.indicator') := by
  use 1, (fun _ => (1 : EReal)), (fun _ => E)
  constructor
  · intro i
    constructor
    · exact hE
    · norm_num
  · ext x
    simp [EReal.indicator, Real.EReal_fun]

/-- Exercise 1.3.1(vi) (Compatibility with Lebesgue measure, integral of an indicator) -/
lemma UnsignedSimpleFunction.integral_indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  (UnsignedSimpleFunction.indicator hE).integ = Lebesgue_measure E := by
  have heq : (Real.toEReal ∘ E.indicator') = ∑ i : Fin 1, (1 : EReal) • EReal.indicator E := by
    ext x
    simp [EReal.indicator, Real.EReal_fun]
  rw [UnsignedSimpleFunction.integral_eq (UnsignedSimpleFunction.indicator hE) (k := 1) (c := fun _ => (1 : EReal))
    (E := fun _ => E) (hmes := fun i => hE) (hnonneg := fun i => by norm_num) (heq := heq)]
  simp

/-! ## Disjoint representation for {name}`RealSimpleFunction`

Measure-theory specific lemmas for the disjoint representation of simple functions. -/

namespace RealSimpleFunction.DisjointRepr

open UnsignedSimpleFunction.IntegralWellDef

/-- Single atoms are measurable -/
lemma singleAtom_measurable {d k : ℕ} {E : Fin k → Set (EuclideanSpace' d)}
    (hE : ∀ i, LebesgueMeasurable (E i)) (n : Fin (2^k)) :
    LebesgueMeasurable (singleAtom E n) := by
  simp only [singleAtom]
  exact atom_measurable hE (fun i => Fin.elim0 i) ⟨n.val, by simp only [add_zero]; exact n.isLt⟩

/-- On a point in singleAtom n, the original sum equals atomValue n -/
lemma sum_indicator_eq_atomValue {d k : ℕ} (c : Fin k → ℝ) (E : Fin k → Set (EuclideanSpace' d))
    (n : Fin (2^k)) (x : EuclideanSpace' d) (hx : x ∈ singleAtom E n) :
    (∑ i : Fin k, (c i) * (E i).indicator' x) = atomValue c n := by
  simp only [atomValue]
  apply Finset.sum_congr rfl
  intro i _
  rw [mem_singleAtom_iff] at hx
  by_cases hbit : (n.val.testBit i.val) = true
  · simp only [hbit, ↓reduceIte]
    have hx_in : x ∈ E i := (hx i).mp hbit
    simp only [Set.indicator'_of_mem hx_in, mul_one]
  · have hbit_false : (n.val.testBit i.val) = false := Bool.eq_false_iff.mpr hbit
    have hx_out : x ∉ E i := fun h => hbit ((hx i).mpr h)
    simp only [Set.indicator'_of_notMem hx_out, mul_zero, hbit_false, Bool.false_eq_true,
      ↓reduceIte]

/-- The original function equals the sum over atoms with atomValue coefficients -/
lemma eq_sum_atomValue_indicator {d k : ℕ} (c : Fin k → ℝ) (E : Fin k → Set (EuclideanSpace' d)) :
    (∑ i : Fin k, (c i) • (E i).indicator') = ∑ n : Fin (2^k), (atomValue c n) • (singleAtom E n).indicator' := by
  classical
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have ⟨n, hn_mem, hn_unique⟩ := exists_unique_singleAtom E x
  have hrhs : (∑ m : Fin (2^k), atomValue c m * (singleAtom E m).indicator' x) = atomValue c n := by
    rw [Finset.sum_eq_single n]
    · simp only [Set.indicator'_of_mem hn_mem, mul_one]
    · intro m _ hm_ne
      have hx_notin : x ∉ singleAtom E m := fun h => hm_ne (hn_unique m h)
      simp only [Set.indicator'_of_notMem hx_notin, mul_zero]
    · intro h; exact absurd (Finset.mem_univ n) h
  rw [hrhs]
  exact sum_indicator_eq_atomValue c E n x hn_mem

end RealSimpleFunction.DisjointRepr

/-- Disjoint representation: any {name}`RealSimpleFunction` has an equivalent representation
    with pairwise disjoint, measurable sets. -/
lemma RealSimpleFunction.disjoint_representation {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) :
    ∃ (n:ℕ) (v: Fin n → ℝ) (A: Fin n → Set (EuclideanSpace' d)),
      (∀ i, LebesgueMeasurable (A i)) ∧
      Set.univ.PairwiseDisjoint A ∧
      f = ∑ i, (v i) • (A i).indicator' := by
  open UnsignedSimpleFunction.IntegralWellDef in
  obtain ⟨k, c, E, hmes, heq⟩ := hf
  use 2^k, UnsignedSimpleFunction.IntegralWellDef.atomValue c,
      UnsignedSimpleFunction.IntegralWellDef.singleAtom E
  refine ⟨?_, ?_, ?_⟩
  · exact fun i => DisjointRepr.singleAtom_measurable hmes i
  · exact UnsignedSimpleFunction.IntegralWellDef.singleAtom_pairwiseDisjoint E
  · rw [heq]
    exact DisjointRepr.eq_sum_atomValue_indicator c E

lemma RealSimpleFunction.abs {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : UnsignedSimpleFunction (EReal.abs_fun f) := by
  obtain ⟨n, v, A, hA_meas, hA_disj, heq⟩ := hf.disjoint_representation
  use n, fun i => (‖v i‖).toEReal, A
  constructor
  · intro i
    constructor
    · exact hA_meas i
    · exact EReal.coe_nonneg.mpr (norm_nonneg (v i))
  · ext x
    simp only [EReal.abs_fun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx_in : ∃ j, x ∈ A j
    · obtain ⟨j, hj⟩ := hx_in
      have hlhs : f x = v j := by
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single j]
        · simp only [Set.indicator'_of_mem hj, mul_one]
        · intro i _ hi_ne
          have hx_notin : x ∉ A i := by
            intro hx_in_i
            have := hA_disj (Set.mem_univ i) (Set.mem_univ j) hi_ne
            simp only [Function.onFun, Set.disjoint_left] at this
            exact this hx_in_i hj
          simp only [Set.indicator'_of_notMem hx_notin, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hrhs : (∑ i : Fin n, (‖v i‖).toEReal * EReal.indicator (A i) x) =
                  (‖v j‖).toEReal := by
        rw [Finset.sum_eq_single j]
        · simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hj, EReal.coe_one, mul_one]
        · intro i _ hi_ne
          have hx_notin : x ∉ A i := by
            intro hx_in_i
            have := hA_disj (Set.mem_univ i) (Set.mem_univ j) hi_ne
            simp only [Function.onFun, Set.disjoint_left] at this
            exact this hx_in_i hj
          simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem hx_notin, EReal.coe_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [hlhs, hrhs]
    · push_neg at hx_in
      have hlhs : f x = 0 := by
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_eq_zero
        intro i _
        simp only [Set.indicator'_of_notMem (hx_in i), mul_zero]
      have hrhs : (∑ i : Fin n, (‖v i‖).toEReal * EReal.indicator (A i) x) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem (hx_in i), EReal.coe_zero, mul_zero]
      rw [hlhs, hrhs]
      simp only [norm_zero, EReal.coe_zero]

open UnsignedSimpleFunction.IntegralWellDef

/-- Complex analogue of {name}`atomValue`: the value on a joint atom. -/
noncomputable def atomValueComplex {k : ℕ} (c : Fin k → ℂ) (n : Fin (2^k)) : ℂ :=
  ∑ i : Fin k, if n.val.testBit i.val then c i else 0

/-- On a point in singleAtom n, the complex sum equals atomValueComplex n. -/
lemma sum_indicator_eq_atomValue_complex {d k : ℕ} (c : Fin k → ℂ)
    (E : Fin k → Set (EuclideanSpace' d)) (n : Fin (2^k)) (x : EuclideanSpace' d)
    (hx : x ∈ singleAtom E n) :
    (∑ i : Fin k, (c i) * (Complex.indicator (E i) x)) = atomValueComplex c n := by
  simp only [atomValueComplex]
  apply Finset.sum_congr rfl
  intro i _
  rw [mem_singleAtom_iff] at hx
  by_cases hbit : (n.val.testBit i.val) = true
  · simp only [hbit, ↓reduceIte]
    have hx_in : x ∈ E i := (hx i).mp hbit
    simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hx_in, Complex.ofReal_one, mul_one]
  · have hbit_false : (n.val.testBit i.val) = false := Bool.eq_false_iff.mpr hbit
    have hx_out : x ∉ E i := fun h => hbit ((hx i).mpr h)
    simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx_out, Complex.ofReal_zero,
      mul_zero, hbit_false, Bool.false_eq_true, ↓reduceIte]

/-- The complex function equals the sum over atoms with atomValueComplex coefficients. -/
lemma eq_sum_atomValue_indicator_complex {d k : ℕ} (c : Fin k → ℂ)
    (E : Fin k → Set (EuclideanSpace' d)) :
    (∑ i : Fin k, (c i) • (Complex.indicator (E i))) =
      ∑ n : Fin (2^k), (atomValueComplex c n) • (Complex.indicator (singleAtom E n)) := by
  classical
  ext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have ⟨n, hn_mem, hn_unique⟩ := exists_unique_singleAtom E x
  have hrhs : (∑ m : Fin (2^k), atomValueComplex c m * Complex.indicator (singleAtom E m) x) =
      atomValueComplex c n := by
    rw [Finset.sum_eq_single n]
    · simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hn_mem, Complex.ofReal_one, mul_one]
    · intro m _ hm_ne
      have hx_notin : x ∉ singleAtom E m := fun h => hm_ne (hn_unique m h)
      simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx_notin, Complex.ofReal_zero, mul_zero]
    · intro h; exact absurd (Finset.mem_univ n) h
  rw [hrhs]
  exact sum_indicator_eq_atomValue_complex c E n x hn_mem

/-- Disjoint representation for complex simple functions. -/
lemma ComplexSimpleFunction.disjoint_representation {d:ℕ} {f: EuclideanSpace' d → ℂ}
    (hf: ComplexSimpleFunction f) :
    ∃ (n:ℕ) (v: Fin n → ℂ) (A: Fin n → Set (EuclideanSpace' d)),
      (∀ i, LebesgueMeasurable (A i)) ∧
      Set.univ.PairwiseDisjoint A ∧
      f = ∑ i, (v i) • (Complex.indicator (A i)) := by
  obtain ⟨k, c, E, hmes, heq⟩ := hf
  use 2^k, atomValueComplex c, singleAtom E
  refine ⟨?_, ?_, ?_⟩
  · exact fun i => RealSimpleFunction.DisjointRepr.singleAtom_measurable hmes i
  · exact singleAtom_pairwiseDisjoint E
  · rw [heq]
    exact eq_sum_atomValue_indicator_complex c E

lemma abs_complex_proof {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : UnsignedSimpleFunction (EReal.abs_fun f) := by
  obtain ⟨n, v, A, hA_meas, hA_disj, heq⟩ := hf.disjoint_representation
  use n, fun i => (‖v i‖).toEReal, A
  constructor
  · intro i
    constructor
    · exact hA_meas i
    · exact EReal.coe_nonneg.mpr (norm_nonneg (v i))
  · ext x
    simp only [EReal.abs_fun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx_in : ∃ j, x ∈ A j
    · obtain ⟨j, hj⟩ := hx_in
      have hlhs : f x = v j := by
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single j]
        · simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hj, Complex.ofReal_one, mul_one]
        · intro i _ hi_ne
          have hx_notin : x ∉ A i := by
            intro hx_in_i
            have := hA_disj (Set.mem_univ i) (Set.mem_univ j) hi_ne
            simp only [Function.onFun, Set.disjoint_left] at this
            exact this hx_in_i hj
          simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx_notin, Complex.ofReal_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hrhs : (∑ i : Fin n, (‖v i‖).toEReal * EReal.indicator (A i) x) =
                  (‖v j‖).toEReal := by
        rw [Finset.sum_eq_single j]
        · simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hj, EReal.coe_one, mul_one]
        · intro i _ hi_ne
          have hx_notin : x ∉ A i := by
            intro hx_in_i
            have := hA_disj (Set.mem_univ i) (Set.mem_univ j) hi_ne
            simp only [Function.onFun, Set.disjoint_left] at this
            exact this hx_in_i hj
          simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem hx_notin, EReal.coe_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [hlhs, hrhs]
    · push_neg at hx_in
      have hlhs : f x = 0 := by
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_eq_zero
        intro i _
        simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem (hx_in i), Complex.ofReal_zero, mul_zero]
      have hrhs : (∑ i : Fin n, (‖v i‖).toEReal * EReal.indicator (A i) x) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem (hx_in i), EReal.coe_zero, mul_zero]
      rw [hlhs, hrhs]
      simp only [norm_zero, EReal.coe_zero]
lemma ComplexSimpleFunction.abs {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : UnsignedSimpleFunction (EReal.abs_fun f) := by
  obtain ⟨n, v, A, hA_meas, hA_disj, heq⟩ := hf.disjoint_representation
  use n, fun i => (‖v i‖).toEReal, A
  constructor
  · intro i
    constructor
    · exact hA_meas i
    · exact EReal.coe_nonneg.mpr (norm_nonneg (v i))
  · ext x
    simp only [EReal.abs_fun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hx_in : ∃ j, x ∈ A j
    · obtain ⟨j, hj⟩ := hx_in
      have hlhs : f x = v j := by
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single j]
        · simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hj, Complex.ofReal_one, mul_one]
        · intro i _ hi_ne
          have hx_notin : x ∉ A i := by
            intro hx_in_i
            have := hA_disj (Set.mem_univ i) (Set.mem_univ j) hi_ne
            simp only [Function.onFun, Set.disjoint_left] at this
            exact this hx_in_i hj
          simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx_notin, Complex.ofReal_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hrhs : (∑ i : Fin n, (‖v i‖).toEReal * EReal.indicator (A i) x) =
                  (‖v j‖).toEReal := by
        rw [Finset.sum_eq_single j]
        · simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hj, EReal.coe_one, mul_one]
        · intro i _ hi_ne
          have hx_notin : x ∉ A i := by
            intro hx_in_i
            have := hA_disj (Set.mem_univ i) (Set.mem_univ j) hi_ne
            simp only [Function.onFun, Set.disjoint_left] at this
            exact this hx_in_i hj
          simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem hx_notin, EReal.coe_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [hlhs, hrhs]
    · push_neg at hx_in
      have hlhs : f x = 0 := by
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_eq_zero
        intro i _
        simp only [Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem (hx_in i), Complex.ofReal_zero, mul_zero]
      have hrhs : (∑ i : Fin n, (‖v i‖).toEReal * EReal.indicator (A i) x) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem (hx_in i), EReal.coe_zero, mul_zero]
      rw [hlhs, hrhs]
      simp only [norm_zero, EReal.coe_zero]

/-- Definition 1.3.6 (Absolutely convergent simple integral) -/
def RealSimpleFunction.AbsolutelyIntegrable {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : Prop :=
  (hf.abs).integ < ⊤

/-- Definition 1.3.6 (Absolutely convergent simple integral) -/
def ComplexSimpleFunction.AbsolutelyIntegrable {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : Prop :=
  (hf.abs).integ < ⊤

def RealSimpleFunction.pos {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : UnsignedSimpleFunction (EReal.pos_fun f) := by
  -- Use disjoint representation: f = ∑ i, v_i • A_i.indicator' with disjoint A_i
  obtain ⟨n, v, A, hA_meas, hA_disj, heq⟩ := hf.disjoint_representation
  -- The positive part is ∑ i, (max(v_i, 0)).toEReal • EReal.indicator(A_i)
  use n, fun i => (max (v i) 0).toEReal, A
  constructor
  · intro i
    constructor
    · exact hA_meas i
    · exact EReal.coe_nonneg.mpr (le_max_right (v i) 0)
  · ext x
    simp only [EReal.pos_fun, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- Since atoms are disjoint, x is in at most one atom
    by_cases hx_in : ∃ j, x ∈ A j
    · -- x is in exactly one atom due to disjointness (we use exists version)
      obtain ⟨j, hj⟩ := hx_in
      -- The sum on both sides only has one nonzero term
      have hlhs : f x = v j := by
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [Finset.sum_eq_single j]
        · simp only [Set.indicator'_of_mem hj, mul_one]
        · intro i _ hi_ne
          have hx_notin : x ∉ A i := by
            intro hx_in_i
            have := hA_disj (Set.mem_univ i) (Set.mem_univ j) hi_ne
            simp only [Function.onFun, Set.disjoint_left] at this
            exact this hx_in_i hj
          simp only [Set.indicator'_of_notMem hx_notin, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      have hrhs : (∑ i : Fin n, (max (v i) 0).toEReal * EReal.indicator (A i) x) =
                  (max (v j) 0).toEReal := by
        rw [Finset.sum_eq_single j]
        · simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_mem hj, EReal.coe_one, mul_one]
        · intro i _ hi_ne
          have hx_notin : x ∉ A i := by
            intro hx_in_i
            have := hA_disj (Set.mem_univ i) (Set.mem_univ j) hi_ne
            simp only [Function.onFun, Set.disjoint_left] at this
            exact this hx_in_i hj
          simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem hx_notin, EReal.coe_zero, mul_zero]
        · intro h; exact absurd (Finset.mem_univ j) h
      rw [hlhs, hrhs]
    · -- x is not in any atom, so f(x) = 0
      push_neg at hx_in
      have hlhs : f x = 0 := by
        rw [heq]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_eq_zero
        intro i _
        simp only [Set.indicator'_of_notMem (hx_in i), mul_zero]
      have hrhs : (∑ i : Fin n, (max (v i) 0).toEReal * EReal.indicator (A i) x) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp only [EReal.indicator, Real.EReal_fun, Set.indicator'_of_notMem (hx_in i), EReal.coe_zero, mul_zero]
      rw [hlhs, hrhs]
      simp only [max_self, EReal.coe_zero]

def RealSimpleFunction.neg {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : UnsignedSimpleFunction (EReal.neg_fun f) := by
  -- neg_fun f = pos_fun (-f), and -f = (-1) • f is a simple function
  have h : EReal.neg_fun f = EReal.pos_fun ((-1 : ℝ) • f) := by
    ext x; simp only [EReal.neg_fun, EReal.pos_fun, Pi.smul_apply, smul_eq_mul, neg_one_mul]
  rw [h]
  exact (hf.smul (-1)).pos

noncomputable def RealSimpleFunction.integ {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : ℝ := (hf.pos).integ.toReal - (hf.neg).integ.toReal

def ComplexSimpleFunction.re {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : RealSimpleFunction (Complex.re_fun f) := by
  -- If f = ∑ i, c_i • Complex.indicator(E_i), then Re(f) = ∑ i, Re(c_i) • indicator'(E_i)
  obtain ⟨k, c, E, hmes, heq⟩ := hf
  use k, fun i => (c i).re, E
  constructor
  · exact hmes
  · ext x
    simp only [Complex.re_fun, heq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- Goal: (∑ i, c i * Complex.indicator (E i) x).re = ∑ i, (c i).re * (E i).indicator' x
    rw [Complex.re_sum]
    congr 1; ext i
    -- Goal: (c i * Complex.indicator (E i) x).re = (c i).re * (E i).indicator' x
    simp only [Complex.indicator, Real.complex_fun]
    rw [Complex.re_mul_ofReal]

def ComplexSimpleFunction.im {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : RealSimpleFunction (Complex.im_fun f) := by
  -- If f = ∑ i, c_i • Complex.indicator(E_i), then Im(f) = ∑ i, Im(c_i) • indicator'(E_i)
  obtain ⟨k, c, E, hmes, heq⟩ := hf
  use k, fun i => (c i).im, E
  constructor
  · exact hmes
  · ext x
    simp only [Complex.im_fun, heq, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    -- Goal: (∑ i, c i * Complex.indicator (E i) x).im = ∑ i, (c i).im * (E i).indicator' x
    rw [Complex.im_sum]
    congr 1; ext i
    -- Goal: (c i * Complex.indicator (E i) x).im = (c i).im * (E i).indicator' x
    simp only [Complex.indicator, Real.complex_fun]
    rw [Complex.im_mul_ofReal]

noncomputable def ComplexSimpleFunction.integ {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : ℂ :=
  hf.re.integ + Complex.I * hf.im.integ

lemma RealSimpleFunction.absolutelyIntegrable_iff {d:ℕ} {f: EuclideanSpace' d → ℝ} (hf: RealSimpleFunction f) : hf.AbsolutelyIntegrable ↔ Lebesgue_measure (Support f) < ⊤ := by
  rw [RealSimpleFunction.AbsolutelyIntegrable]
  rw [UnsignedSimpleFunction.integral_finite_iff (hf.abs)]
  have hsup : Support (EReal.abs_fun f) = Support f := by
    ext x
    simp [Support, EReal.abs_fun]
  have haa : AlmostAlways (fun x ↦ EReal.abs_fun f x < ⊤) := by
    unfold AlmostAlways
    apply IsNull.subset (Lebesgue_outer_measure.of_empty d)
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [EReal.abs_fun] at hx
    exact absurd (EReal.coe_lt_top (‖f x‖)) hx
  constructor
  · intro h
    rcases h with ⟨_, hmsup⟩
    simpa [hsup] using hmsup
  · intro hmsup
    exact ⟨haa, by simpa [hsup] using hmsup⟩

lemma ComplexSimpleFunction.absolutelyIntegrable_iff {d:ℕ} {f: EuclideanSpace' d → ℂ} (hf: ComplexSimpleFunction f) : hf.AbsolutelyIntegrable ↔ Lebesgue_measure (Support f) < ⊤ := by
  rw [ComplexSimpleFunction.AbsolutelyIntegrable]
  rw [UnsignedSimpleFunction.integral_finite_iff (hf.abs)]
  have hsup : Support (EReal.abs_fun f) = Support f := by
    ext x
    simp [Support, EReal.abs_fun]
  have haa : AlmostAlways (fun x ↦ EReal.abs_fun f x < ⊤) := by
    unfold AlmostAlways
    apply IsNull.subset (Lebesgue_outer_measure.of_empty d)
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [EReal.abs_fun] at hx
    exact absurd (EReal.coe_lt_top (‖f x‖)) hx
  constructor
  · intro h
    rcases h with ⟨_, hmsup⟩
    simpa [hsup] using hmsup
  · intro hmsup
    exact ⟨haa, by simpa [hsup] using hmsup⟩

lemma RealSimpleFunction.AbsolutelyIntegrable.add {d:ℕ} {f g: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} {hg: RealSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) :
  (hf.add hg).AbsolutelyIntegrable := by

  rw [RealSimpleFunction.absolutelyIntegrable_iff] at hf_integ hg_integ ⊢
  have hsub : Support (f + g) ⊆ Support f ∪ Support g := by
    intro x hx
    simp [Support] at hx ⊢
    by_contra h
    push_neg at h
    exact hx (by simp [h.1, h.2])
  have hle : Lebesgue_measure (Support f ∪ Support g) ≤ Lebesgue_measure (Support f) + Lebesgue_measure (Support g) := by
    let E' : Fin 2 → Set (EuclideanSpace' d) := ![Support f, Support g]
    have h_union : Support f ∪ Support g = ⋃ i, E' i := by
      simp only [E']
      ext x
      simp
    have h_sum : ∑ i : Fin 2, Lebesgue_outer_measure (E' i) = Lebesgue_measure (Support f) + Lebesgue_measure (Support g) := by
      simp [Fin.sum_univ_two, E', Lebesgue_measure]
    rw [h_union, ← h_sum]
    exact Lebesgue_outer_measure.finite_union_le E'
  have h_fin : Lebesgue_measure (Support f) + Lebesgue_measure (Support g) < ⊤ :=
    EReal.add_lt_top (ne_of_lt hf_integ) (ne_of_lt hg_integ)
  exact lt_of_le_of_lt (le_trans (Lebesgue_outer_measure.mono hsub) hle) h_fin

lemma ComplexSimpleFunction.AbsolutelyIntegrable.add {d:ℕ} {f g: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} {hg: ComplexSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) :
  (hf.add hg).AbsolutelyIntegrable := by
  rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hf_integ hg_integ ⊢
  have hsub : Support (f + g) ⊆ Support f ∪ Support g := by
    intro x hx
    simp [Support] at hx ⊢
    by_contra h
    push_neg at h
    exact hx (by simp [h.1, h.2])
  have hle : Lebesgue_measure (Support f ∪ Support g) ≤ Lebesgue_measure (Support f) + Lebesgue_measure (Support g) := by
    let E' : Fin 2 → Set (EuclideanSpace' d) := ![Support f, Support g]
    have h_union : Support f ∪ Support g = ⋃ i, E' i := by
      simp only [E']
      ext x
      simp
    have h_sum : ∑ i : Fin 2, Lebesgue_outer_measure (E' i) = Lebesgue_measure (Support f) + Lebesgue_measure (Support g) := by
      simp [Fin.sum_univ_two, E', Lebesgue_measure]
    rw [h_union, ← h_sum]
    exact Lebesgue_outer_measure.finite_union_le E'
  have h_fin : Lebesgue_measure (Support f) + Lebesgue_measure (Support g) < ⊤ :=
    EReal.add_lt_top (ne_of_lt hf_integ) (ne_of_lt hg_integ)
  exact lt_of_le_of_lt (le_trans (Lebesgue_outer_measure.mono hsub) hle) h_fin


lemma RealSimpleFunction.AbsolutelyIntegrable.smul {d:ℕ} {f: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) (a: ℝ) :
  (hf.smul a).AbsolutelyIntegrable := by
  rw [RealSimpleFunction.absolutelyIntegrable_iff] at hf_integ ⊢
  by_cases ha : a = 0
  · have hsub : Support (a • f) ⊆ (∅ : Set (EuclideanSpace' d)) := by
      intro x hx
      simp [Support, Pi.smul_apply, ha] at hx
    have hzero : Lebesgue_measure (Support (a • f)) = 0 := by
      apply le_antisymm _ (Lebesgue_outer_measure.nonneg _)
      have hle : Lebesgue_measure (Support (a • f)) ≤ Lebesgue_measure (∅ : Set (EuclideanSpace' d)) :=
        Lebesgue_outer_measure.mono hsub
      simpa [Lebesgue_outer_measure.of_empty] using hle
    rw [hzero]
    exact EReal.zero_lt_top
  · have hsup_eq : Support (a • f) = Support f := by
      ext x
      simp only [Support, Pi.smul_apply, Set.mem_setOf_eq]
      constructor
      · intro hx
        exact (mul_ne_zero_iff.mp hx).2
      · intro hx
        exact mul_ne_zero_iff.mpr ⟨ha, hx⟩
    rw [hsup_eq]
    exact hf_integ


lemma ComplexSimpleFunction.AbsolutelyIntegrable.smul {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) (a: ℂ) :
  (hf.smul a).AbsolutelyIntegrable := by
  rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hf_integ ⊢
  by_cases ha : a = 0
  · have hsub : Support (a • f) ⊆ (∅ : Set (EuclideanSpace' d)) := by
      intro x hx
      simp [Support, Pi.smul_apply, ha] at hx
    have hzero : Lebesgue_measure (Support (a • f)) = 0 := by
      apply le_antisymm _ (Lebesgue_outer_measure.nonneg _)
      have hle : Lebesgue_measure (Support (a • f)) ≤ Lebesgue_measure (∅ : Set (EuclideanSpace' d)) :=
        Lebesgue_outer_measure.mono hsub
      simpa [Lebesgue_outer_measure.of_empty] using hle
    rw [hzero]
    exact EReal.zero_lt_top
  · have hsup_eq : Support (a • f) = Support f := by
      ext x
      simp only [Support, Pi.smul_apply, Set.mem_setOf_eq]
      constructor
      · intro hx
        exact (mul_ne_zero_iff.mp hx).2
      · intro hx
        exact mul_ne_zero_iff.mpr ⟨ha, hx⟩
    rw [hsup_eq]
    exact hf_integ


lemma ComplexSimpleFunction.AbsolutelyIntegrable.conj {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) :
  (hf.conj).AbsolutelyIntegrable := by
  rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hf_integ ⊢
  have hsup : Support (Complex.conj_fun f) = Support f := by
    ext x
    simp [Support, Complex.conj_fun]
  rw [hsup]
  exact hf_integ

/-- Exercise 1.3.2 (i) ({lit}`*`-linearity) -/
private lemma max_sub_neg (t : ℝ) : max t 0 - max (-t) 0 = t := by
  by_cases h : 0 ≤ t
  · have ht : max t 0 = t := max_eq_left h
    have hneg : max (-t) 0 = 0 := max_eq_right (neg_nonpos.mpr h)
    rw [ht, hneg]
    ring
  · have ht : max t 0 = 0 := max_eq_right (le_of_not_ge h)
    have hneg : max (-t) 0 = -t := max_eq_left (by linarith)
    rw [ht, hneg]
    ring

private lemma pos_neg_add_id (a b : ℝ) :
    max (a + b) 0 + max (-a) 0 + max (-b) 0 = max a 0 + max b 0 + max (-(a + b)) 0 := by
  have ha : max a 0 - max (-a) 0 = a := max_sub_neg a
  have hb : max b 0 - max (-b) 0 = b := max_sub_neg b
  have hab : max (a + b) 0 - max (-(a + b)) 0 = a + b := max_sub_neg (a + b)
  linarith

private lemma unsigned_integral_nonneg {d:ℕ} {f: EuclideanSpace' d → EReal} (hf: UnsignedSimpleFunction f) : 0 ≤ hf.integ := by
  have hf0 : UnsignedSimpleFunction f := hf
  obtain ⟨k, c, E, hmes_nonneg, heq⟩ := hf0
  have hmes : ∀ i, LebesgueMeasurable (E i) := fun i => (hmes_nonneg i).1
  have hnonneg : ∀ i, c i ≥ 0 := fun i => (hmes_nonneg i).2
  have hinteg : hf.integ = ∑ i, c i * Lebesgue_measure (E i) :=
    UnsignedSimpleFunction.integral_eq hf (hmes := hmes) (hnonneg := hnonneg) (heq := heq)
  rw [hinteg]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hnonneg i) (Lebesgue_outer_measure.nonneg (E i)))

private lemma pos_fun_le_abs (t : ℝ) : max t 0 ≤ ‖t‖ := by
  rw [Real.norm_eq_abs]
  exact max_le (le_abs_self t) (abs_nonneg t)

private lemma neg_fun_le_abs (t : ℝ) : max (-t) 0 ≤ ‖t‖ := by
  rw [Real.norm_eq_abs]
  exact max_le (neg_le_abs t) (abs_nonneg t)

private lemma toReal_add_fin {a b : EReal} (ha0 : 0 ≤ a) (ha : a < ⊤) (hb0 : 0 ≤ b) (hb : b < ⊤) :
    (a + b).toReal = a.toReal + b.toReal := by
  apply EReal.toReal_add
  · exact ne_of_lt ha
  · exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe 0) ha0)
  · exact ne_of_lt hb
  · exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe 0) hb0)

lemma RealSimpleFunction.integ_add {d:ℕ} {f g: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} {hg: RealSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) : (hf.add hg).integ = hf.integ + hg.integ := by
  -- Step 1: pointwise identity
  have h_point : ∀ x, EReal.pos_fun (f + g) x + EReal.neg_fun f x + EReal.neg_fun g x =
      EReal.pos_fun f x + EReal.pos_fun g x + EReal.neg_fun (f + g) x := by
    intro x
    simp only [EReal.pos_fun, EReal.neg_fun, Pi.add_apply]
    simp only [← EReal.coe_add]
    congr 1
    exact pos_neg_add_id (f x) (g x)
  -- Step 2: EReal integral identity
  have hae : AlmostEverywhereEqual ((EReal.pos_fun (f + g) + EReal.neg_fun f) + EReal.neg_fun g)
      ((EReal.pos_fun f + EReal.pos_fun g) + EReal.neg_fun (f + g)) :=
    AlmostAlways.ofAlways h_point
  let hp : UnsignedSimpleFunction (EReal.pos_fun (f + g)) := (hf.add hg).pos
  let hnf : UnsignedSimpleFunction (EReal.neg_fun f) := hf.neg
  let hng : UnsignedSimpleFunction (EReal.neg_fun g) := hg.neg
  let hpf : UnsignedSimpleFunction (EReal.pos_fun f) := hf.pos
  let hpg : UnsignedSimpleFunction (EReal.pos_fun g) := hg.pos
  let hn : UnsignedSimpleFunction (EReal.neg_fun (f + g)) := (hf.add hg).neg
  have h_int : ((hp.add hnf).add hng).integ = ((hpf.add hpg).add hn).integ :=
    UnsignedSimpleFunction.integral_eq_integral_of_aeEqual ((hp.add hnf).add hng) ((hpf.add hpg).add hn) hae
  have h_id : hp.integ + hnf.integ + hng.integ = hpf.integ + hpg.integ + hn.integ := by
    have h1 := UnsignedSimpleFunction.integral_add hp hnf
    have h2 := UnsignedSimpleFunction.integral_add (hp.add hnf) hng
    have h3 := UnsignedSimpleFunction.integral_add hpf hpg
    have h4 := UnsignedSimpleFunction.integral_add (hpf.add hpg) hn
    rw [h2, h1, h4, h3] at h_int
    exact h_int
  -- Step 3: finiteness of all six integrals
  have hfg_ai : (hf.add hg).AbsolutelyIntegrable := RealSimpleFunction.AbsolutelyIntegrable.add hf_integ hg_integ
  have hfg_pos_lt : (hf.add hg).pos.integ < ⊤ := by
    refine lt_of_le_of_lt ?_ hfg_ai
    exact UnsignedSimpleFunction.integral_le_integral_of_aeLe (hf.add hg).pos (hf.add hg).abs
      (AlmostAlways.ofAlways (fun x => by
        simp only [EReal.pos_fun, EReal.abs_fun]
        exact EReal.coe_le_coe_iff.mpr (pos_fun_le_abs ((f + g) x))))
  have hfg_neg_lt : (hf.add hg).neg.integ < ⊤ := by
    refine lt_of_le_of_lt ?_ hfg_ai
    exact UnsignedSimpleFunction.integral_le_integral_of_aeLe (hf.add hg).neg (hf.add hg).abs
      (AlmostAlways.ofAlways (fun x => by
        simp only [EReal.neg_fun, EReal.abs_fun]
        exact EReal.coe_le_coe_iff.mpr (neg_fun_le_abs ((f + g) x))))
  have hf_pos_lt : hf.pos.integ < ⊤ := by
    refine lt_of_le_of_lt ?_ hf_integ
    exact UnsignedSimpleFunction.integral_le_integral_of_aeLe hf.pos hf.abs
      (AlmostAlways.ofAlways (fun x => by
        simp only [EReal.pos_fun, EReal.abs_fun]
        exact EReal.coe_le_coe_iff.mpr (pos_fun_le_abs (f x))))
  have hf_neg_lt : hf.neg.integ < ⊤ := by
    refine lt_of_le_of_lt ?_ hf_integ
    exact UnsignedSimpleFunction.integral_le_integral_of_aeLe hf.neg hf.abs
      (AlmostAlways.ofAlways (fun x => by
        simp only [EReal.neg_fun, EReal.abs_fun]
        exact EReal.coe_le_coe_iff.mpr (neg_fun_le_abs (f x))))
  have hg_pos_lt : hg.pos.integ < ⊤ := by
    refine lt_of_le_of_lt ?_ hg_integ
    exact UnsignedSimpleFunction.integral_le_integral_of_aeLe hg.pos hg.abs
      (AlmostAlways.ofAlways (fun x => by
        simp only [EReal.pos_fun, EReal.abs_fun]
        exact EReal.coe_le_coe_iff.mpr (pos_fun_le_abs (g x))))
  have hg_neg_lt : hg.neg.integ < ⊤ := by
    refine lt_of_le_of_lt ?_ hg_integ
    exact UnsignedSimpleFunction.integral_le_integral_of_aeLe hg.neg hg.abs
      (AlmostAlways.ofAlways (fun x => by
        simp only [EReal.neg_fun, EReal.abs_fun]
        exact EReal.coe_le_coe_iff.mpr (neg_fun_le_abs (g x))))
  have hfg_pos_nn : 0 ≤ (hf.add hg).pos.integ := unsigned_integral_nonneg (hf.add hg).pos
  have hfg_neg_nn : 0 ≤ (hf.add hg).neg.integ := unsigned_integral_nonneg (hf.add hg).neg
  have hf_pos_nn : 0 ≤ hf.pos.integ := unsigned_integral_nonneg hf.pos
  have hf_neg_nn : 0 ≤ hf.neg.integ := unsigned_integral_nonneg hf.neg
  have hg_pos_nn : 0 ≤ hg.pos.integ := unsigned_integral_nonneg hg.pos
  have hg_neg_nn : 0 ≤ hg.neg.integ := unsigned_integral_nonneg hg.neg
  -- Step 4: push toReal through the EReal identity
  have hL : (hp.integ + hnf.integ + hng.integ).toReal =
      hp.integ.toReal + hnf.integ.toReal + hng.integ.toReal := by
    rw [toReal_add_fin (add_nonneg hfg_pos_nn hf_neg_nn)
        (EReal.add_lt_top (ne_of_lt hfg_pos_lt) (ne_of_lt hf_neg_lt)) hg_neg_nn hg_neg_lt]
    rw [toReal_add_fin hfg_pos_nn hfg_pos_lt hf_neg_nn hf_neg_lt]
  have hR : (hpf.integ + hpg.integ + hn.integ).toReal =
      hpf.integ.toReal + hpg.integ.toReal + hn.integ.toReal := by
    rw [toReal_add_fin (add_nonneg hf_pos_nn hg_pos_nn)
        (EReal.add_lt_top (ne_of_lt hf_pos_lt) (ne_of_lt hg_pos_lt)) hfg_neg_nn hfg_neg_lt]
    rw [toReal_add_fin hf_pos_nn hf_pos_lt hg_pos_nn hg_pos_lt]
  have h_toReal : hp.integ.toReal + hnf.integ.toReal + hng.integ.toReal =
      hpf.integ.toReal + hpg.integ.toReal + hn.integ.toReal := by
    have h' : (hp.integ + hnf.integ + hng.integ).toReal =
        (hpf.integ + hpg.integ + hn.integ).toReal := congrArg EReal.toReal h_id
    rw [hL, hR] at h'
    exact h'
  -- Step 5: real algebra
  change hp.integ.toReal - hn.integ.toReal =
    (hpf.integ.toReal - hnf.integ.toReal) + (hpg.integ.toReal - hng.integ.toReal)
  linarith

lemma ComplexSimpleFunction.integ_add {d:ℕ} {f g: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} {hg: ComplexSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) : (hf.add hg).integ = hf.integ + hg.integ := by

  -- (hf.add hg).re = hf.re.add hg.re and similarly for im (Prop proof irrelevance;
  -- the underlying functions agree since Complex.re_fun (f + g) = Complex.re_fun f + Complex.re_fun g is rfl)
  have h_re : (hf.add hg).re = hf.re.add hg.re := by
    exact Subsingleton.elim _ _
  have h_im : (hf.add hg).im = hf.im.add hg.im := by
    exact Subsingleton.elim _ _
  -- transport the equalities through the integral
  have h_re_int : (hf.add hg).re.integ = (hf.re.add hg.re).integ := by
    exact congrArg (fun p : RealSimpleFunction (Complex.re_fun (f + g)) => p.integ) h_re
  have h_im_int : (hf.add hg).im.integ = (hf.im.add hg.im).integ := by
    exact congrArg (fun p : RealSimpleFunction (Complex.im_fun (f + g)) => p.integ) h_im
  -- finiteness of the real/imag parts of f and g
  have hf_re_ai : hf.re.AbsolutelyIntegrable := by
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hf_integ
    have hsub : Support (Complex.re_fun f) ⊆ Support f := by
      intro x hx
      simp only [Support, Set.mem_setOf_eq] at hx ⊢
      intro hzero
      change Complex.re (f x) ≠ 0 at hx
      rw [hzero] at hx
      exact hx (by simp)
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hf_integ
  have hf_im_ai : hf.im.AbsolutelyIntegrable := by
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hf_integ
    have hsub : Support (Complex.im_fun f) ⊆ Support f := by
      intro x hx
      simp only [Support, Set.mem_setOf_eq] at hx ⊢
      intro hzero
      change Complex.im (f x) ≠ 0 at hx
      rw [hzero] at hx
      exact hx (by simp)
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hf_integ
  have hg_re_ai : hg.re.AbsolutelyIntegrable := by
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hg_integ
    have hsub : Support (Complex.re_fun g) ⊆ Support g := by
      intro x hx
      simp only [Support, Set.mem_setOf_eq] at hx ⊢
      intro hzero
      change Complex.re (g x) ≠ 0 at hx
      rw [hzero] at hx
      exact hx (by simp)
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hg_integ
  have hg_im_ai : hg.im.AbsolutelyIntegrable := by
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hg_integ
    have hsub : Support (Complex.im_fun g) ⊆ Support g := by
      intro x hx
      simp only [Support, Set.mem_setOf_eq] at hx ⊢
      intro hzero
      change Complex.im (g x) ≠ 0 at hx
      rw [hzero] at hx
      exact hx (by simp)
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hg_integ
  -- main computation
  unfold ComplexSimpleFunction.integ
  rw [h_re_int, h_im_int]
  have h1 : (hf.re.add hg.re).integ = hf.re.integ + hg.re.integ :=
    RealSimpleFunction.integ_add hf_re_ai hg_re_ai
  have h2 : (hf.im.add hg.im).integ = hf.im.integ + hg.im.integ :=
    RealSimpleFunction.integ_add hf_im_ai hg_im_ai
  rw [h1, h2]
  simp [Complex.ofReal_add]
  ring

/-- Exercise 1.3.2 (i) ({lit}`*`-linearity) -/
private lemma pos_fun_smul_nonneg {X: Type*} (f: X → ℝ) (c: ℝ) (hc: 0 ≤ c) :
    EReal.pos_fun (c • f) = (c : EReal) • EReal.pos_fun f := by
  funext x
  simp only [EReal.pos_fun, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [← mul_zero c, (mul_max_of_nonneg (f x) 0 hc).symm, mul_zero]

private lemma neg_fun_smul_nonneg {X: Type*} (f: X → ℝ) (c: ℝ) (hc: 0 ≤ c) :
    EReal.neg_fun (c • f) = (c : EReal) • EReal.neg_fun f := by
  funext x
  simp only [EReal.neg_fun, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [show -(c * f x) = c * (-f x) from by ring]
  rw [← mul_zero c, (mul_max_of_nonneg (-f x) 0 hc).symm, mul_zero]

private lemma pos_fun_smul_neg {X: Type*} (f: X → ℝ) (c: ℝ) (hc: c < 0) :
    EReal.pos_fun (c • f) = ((-c) : EReal) • EReal.neg_fun f := by
  funext x
  simp only [EReal.pos_fun, EReal.neg_fun, Pi.smul_apply, smul_eq_mul]
  have hnc : 0 ≤ -c := neg_nonneg.mpr (le_of_lt hc)
  congr 1
  rw [show c * f x = (-c) * (-f x) from by ring]
  rw [← mul_zero (-c), (mul_max_of_nonneg (-f x) 0 hnc).symm, mul_zero]

private lemma neg_fun_smul_neg {X: Type*} (f: X → ℝ) (c: ℝ) (hc: c < 0) :
    EReal.neg_fun (c • f) = ((-c) : EReal) • EReal.pos_fun f := by
  funext x
  simp only [EReal.pos_fun, EReal.neg_fun, Pi.smul_apply, smul_eq_mul]
  have hnc : 0 ≤ -c := neg_nonneg.mpr (le_of_lt hc)
  congr 1
  rw [show -(c * f x) = (-c) * f x from by ring]
  rw [← mul_zero (-c), (mul_max_of_nonneg (f x) 0 hnc).symm, mul_zero]

lemma RealSimpleFunction.integ_smul {d:ℕ} {f: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) (a: ℝ) : (hf.smul a).integ = a * hf.integ := by

  have _hfi : hf.AbsolutelyIntegrable := hf_integ
  by_cases ha : 0 ≤ a
  · -- Case a ≥ 0
    have h_pos : EReal.pos_fun (a • f) = (a : EReal) • EReal.pos_fun f := pos_fun_smul_nonneg f a ha
    have h_neg : EReal.neg_fun (a • f) = (a : EReal) • EReal.neg_fun f := neg_fun_smul_nonneg f a ha
    have ha' : (0 : EReal) ≤ (a : EReal) := EReal.coe_nonneg.mpr ha
    have hpos_eq : (hf.smul a).pos.integ = (a : EReal) * hf.pos.integ := by
      have h_eq_ae : AlmostEverywhereEqual (EReal.pos_fun (a • f)) ((a : EReal) • EReal.pos_fun f) :=
        AlmostAlways.ofAlways (fun x => congrFun h_pos x)
      have h_ie : (hf.smul a).pos.integ = (hf.pos.smul ha').integ :=
        UnsignedSimpleFunction.integral_eq_integral_of_aeEqual (hf.smul a).pos (hf.pos.smul ha') h_eq_ae
      rw [h_ie]
      exact UnsignedSimpleFunction.integral_smul hf.pos ha'
    have hneg_eq : (hf.smul a).neg.integ = (a : EReal) * hf.neg.integ := by
      have h_eq_ae : AlmostEverywhereEqual (EReal.neg_fun (a • f)) ((a : EReal) • EReal.neg_fun f) :=
        AlmostAlways.ofAlways (fun x => congrFun h_neg x)
      have h_ie : (hf.smul a).neg.integ = (hf.neg.smul ha').integ :=
        UnsignedSimpleFunction.integral_eq_integral_of_aeEqual (hf.smul a).neg (hf.neg.smul ha') h_eq_ae
      rw [h_ie]
      exact UnsignedSimpleFunction.integral_smul hf.neg ha'
    have h_toReal : ((a : EReal) * hf.pos.integ).toReal - ((a : EReal) * hf.neg.integ).toReal =
        a * (hf.pos.integ.toReal - hf.neg.integ.toReal) := by
      rw [EReal.toReal_mul, EReal.toReal_mul, EReal.toReal_coe]
      ring
    simp only [RealSimpleFunction.integ]
    rw [hpos_eq, hneg_eq]
    exact h_toReal
  · -- Case a < 0
    have ha_neg : a < 0 := lt_of_not_ge ha
    have h_pos : EReal.pos_fun (a • f) = ((-a) : EReal) • EReal.neg_fun f := pos_fun_smul_neg f a ha_neg
    have h_neg : EReal.neg_fun (a • f) = ((-a) : EReal) • EReal.pos_fun f := neg_fun_smul_neg f a ha_neg
    have hb : 0 ≤ -a := neg_nonneg.mpr (le_of_lt ha_neg)
    have hb' : (0 : EReal) ≤ ((-a) : EReal) := EReal.coe_nonneg.mpr hb
    have hpos_eq : (hf.smul a).pos.integ = ((-a) : EReal) * hf.neg.integ := by
      have h_eq_ae : AlmostEverywhereEqual (EReal.pos_fun (a • f)) ((-a : EReal) • EReal.neg_fun f) :=
        AlmostAlways.ofAlways (fun x => congrFun h_pos x)
      have h_ie : (hf.smul a).pos.integ = (hf.neg.smul hb').integ :=
        UnsignedSimpleFunction.integral_eq_integral_of_aeEqual (hf.smul a).pos (hf.neg.smul hb') h_eq_ae
      rw [h_ie]
      exact UnsignedSimpleFunction.integral_smul hf.neg hb'
    have hneg_eq : (hf.smul a).neg.integ = ((-a) : EReal) * hf.pos.integ := by
      have h_eq_ae : AlmostEverywhereEqual (EReal.neg_fun (a • f)) ((-a : EReal) • EReal.pos_fun f) :=
        AlmostAlways.ofAlways (fun x => congrFun h_neg x)
      have h_ie : (hf.smul a).neg.integ = (hf.pos.smul hb').integ :=
        UnsignedSimpleFunction.integral_eq_integral_of_aeEqual (hf.smul a).neg (hf.pos.smul hb') h_eq_ae
      rw [h_ie]
      exact UnsignedSimpleFunction.integral_smul hf.pos hb'
    have h_toReal : (((-a) : EReal) * hf.neg.integ).toReal - (((-a) : EReal) * hf.pos.integ).toReal =
        a * (hf.pos.integ.toReal - hf.neg.integ.toReal) := by
      simp only [EReal.toReal_mul, EReal.toReal_neg_eq, EReal.toReal_coe]
      ring
    simp only [RealSimpleFunction.integ]
    rw [hpos_eq, hneg_eq]
    exact h_toReal

private lemma integ_eq_of_fun_eq {d:ℕ} {f g : EuclideanSpace' d → ℝ} {hf : RealSimpleFunction f} {hg : RealSimpleFunction g}
    (hfg : f = g) : hf.integ = hg.integ := by
  have h_ae_pos : AlmostEverywhereEqual (EReal.pos_fun f) (EReal.pos_fun g) :=
    AlmostAlways.ofAlways (fun x => congrFun (congrArg EReal.pos_fun hfg) x)
  have h_pos_eq : hf.pos.integ = hg.pos.integ :=
    UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hf.pos hg.pos h_ae_pos
  have h_ae_neg : AlmostEverywhereEqual (EReal.neg_fun f) (EReal.neg_fun g) :=
    AlmostAlways.ofAlways (fun x => congrFun (congrArg EReal.neg_fun hfg) x)
  have h_neg_eq : hf.neg.integ = hg.neg.integ :=
    UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hf.neg hg.neg h_ae_neg
  simp [RealSimpleFunction.integ, h_pos_eq, h_neg_eq]

lemma ComplexSimpleFunction.integ_smul {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) (a: ℂ) : (hf.smul a).integ = a * hf.integ := by


  -- re/im parts of f are absolutely integrable
  have hf_re_ai : hf.re.AbsolutelyIntegrable := by
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hf_integ
    have hsub : Support (Complex.re_fun f) ⊆ Support f := by
      intro x hx
      simp only [Support, Set.mem_setOf_eq] at hx ⊢
      intro hzero
      change Complex.re (f x) ≠ 0 at hx
      rw [hzero] at hx
      exact hx (by simp)
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hf_integ
  have hf_im_ai : hf.im.AbsolutelyIntegrable := by
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hf_integ
    have hsub : Support (Complex.im_fun f) ⊆ Support f := by
      intro x hx
      simp only [Support, Set.mem_setOf_eq] at hx ⊢
      intro hzero
      change Complex.im (f x) ≠ 0 at hx
      rw [hzero] at hx
      exact hx (by simp)
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hf_integ

  -- pointwise re/im of a • f
  have h_pt_re : Complex.re_fun (a • f) = a.re • Complex.re_fun f + (-a.im) • Complex.im_fun f := by
    funext x
    simp only [Complex.re_fun, Complex.im_fun, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [Complex.mul_re]
    change a.re * (f x).re - a.im * (f x).im = a.re * (f x).re + (-a.im) * (f x).im
    ring
  have h_pt_im : Complex.im_fun (a • f) = a.re • Complex.im_fun f + a.im • Complex.re_fun f := by
    funext x
    simp only [Complex.re_fun, Complex.im_fun, Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [Complex.mul_im]

  -- transport through the integral
  have h_re_int : (hf.smul a).re.integ = ((hf.re.smul a.re).add (hf.im.smul (-a.im))).integ := by
    apply integ_eq_of_fun_eq
    exact h_pt_re
  have h_im_int : (hf.smul a).im.integ = ((hf.im.smul a.re).add (hf.re.smul a.im)).integ := by
    apply integ_eq_of_fun_eq
    exact h_pt_im

  -- additivity / smul linearity of the real integral for the pieces
  have h1 : ((hf.re.smul a.re).add (hf.im.smul (-a.im))).integ = (hf.re.smul a.re).integ + (hf.im.smul (-a.im)).integ :=
    RealSimpleFunction.integ_add (RealSimpleFunction.AbsolutelyIntegrable.smul hf_re_ai a.re) (RealSimpleFunction.AbsolutelyIntegrable.smul hf_im_ai (-a.im))
  have h2 : ((hf.im.smul a.re).add (hf.re.smul a.im)).integ = (hf.im.smul a.re).integ + (hf.re.smul a.im).integ :=
    RealSimpleFunction.integ_add (RealSimpleFunction.AbsolutelyIntegrable.smul hf_im_ai a.re) (RealSimpleFunction.AbsolutelyIntegrable.smul hf_re_ai a.im)
  have h3 : (hf.re.smul a.re).integ = a.re * hf.re.integ := RealSimpleFunction.integ_smul hf_re_ai a.re
  have h4 : (hf.im.smul (-a.im)).integ = (-a.im) * hf.im.integ := RealSimpleFunction.integ_smul hf_im_ai (-a.im)
  have h5 : (hf.im.smul a.re).integ = a.re * hf.im.integ := RealSimpleFunction.integ_smul hf_im_ai a.re
  have h6 : (hf.re.smul a.im).integ = a.im * hf.re.integ := RealSimpleFunction.integ_smul hf_re_ai a.im

  -- main computation: compare re/im components
  unfold ComplexSimpleFunction.integ
  rw [h_re_int, h_im_int, h1, h2, h3, h4, h5, h6]
  apply Complex.ext
  · simp
    ring
  · simp

/-- Exercise 1.3.2 (i) ({lit}`*`-linearity, conjugation) -/
lemma ComplexSimpleFunction.integral_conj {d:ℕ} {f: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} (hf_integ: hf.AbsolutelyIntegrable) : (hf.conj).integ = (starRingEnd ℂ) hf.integ := by


  -- re/im parts of f are absolutely integrable
  have hf_re_ai : hf.re.AbsolutelyIntegrable := by
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hf_integ
    have hsub : Support (Complex.re_fun f) ⊆ Support f := by
      intro x hx
      simp only [Support, Set.mem_setOf_eq] at hx ⊢
      intro hzero
      change Complex.re (f x) ≠ 0 at hx
      rw [hzero] at hx
      exact hx (by simp)
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hf_integ
  have hf_im_ai : hf.im.AbsolutelyIntegrable := by
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hf_integ
    have hsub : Support (Complex.im_fun f) ⊆ Support f := by
      intro x hx
      simp only [Support, Set.mem_setOf_eq] at hx ⊢
      intro hzero
      change Complex.im (f x) ≠ 0 at hx
      rw [hzero] at hx
      exact hx (by simp)
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hf_integ

  -- pointwise re/im of conj f
  have h_pt_re : Complex.re_fun (Complex.conj_fun f) = Complex.re_fun f := by
    funext x
    simp [Complex.re_fun, Complex.conj_fun, Complex.conj_re]
  have h_pt_im : Complex.im_fun (Complex.conj_fun f) = (-1 : ℝ) • Complex.im_fun f := by
    funext x
    simp [Complex.im_fun, Complex.conj_fun, Complex.conj_im]

  -- transport through the integral
  have h_re_int : (hf.conj).re.integ = hf.re.integ := by
    apply integ_eq_of_fun_eq
    exact h_pt_re
  have h_im_int : (hf.conj).im.integ = (hf.im.smul (-1 : ℝ)).integ := by
    apply integ_eq_of_fun_eq
    exact h_pt_im

  -- main computation
  unfold ComplexSimpleFunction.integ
  rw [h_re_int, h_im_int, RealSimpleFunction.integ_smul hf_im_ai (-1 : ℝ)]
  rw [map_add, map_mul]
  simp [Complex.conj_ofReal, Complex.conj_I]

/-- Exercise 1.3.2 (ii) (equivalence) -/
lemma RealSimpleFunction.integral_eq_integral_of_aeEqual {d:ℕ} {f g: EuclideanSpace' d → ℝ} {hf: RealSimpleFunction f} {hg: RealSimpleFunction g} (_hf_integ: hf.AbsolutelyIntegrable) (_hg_integ: hg.AbsolutelyIntegrable) (h_ae: AlmostEverywhereEqual f g) : hf.integ = hg.integ := by

  have h_ae_pos : AlmostEverywhereEqual (EReal.pos_fun f) (EReal.pos_fun g) :=
    AlmostAlways.mp h_ae (fun x hx => by simp [EReal.pos_fun, hx])
  have h_pos_eq : hf.pos.integ = hg.pos.integ :=
    UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hf.pos hg.pos h_ae_pos
  have h_ae_neg : AlmostEverywhereEqual (EReal.neg_fun f) (EReal.neg_fun g) :=
    AlmostAlways.mp h_ae (fun x hx => by simp [EReal.neg_fun, hx])
  have h_neg_eq : hf.neg.integ = hg.neg.integ :=
    UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hf.neg hg.neg h_ae_neg
  simp [RealSimpleFunction.integ, h_pos_eq, h_neg_eq]

lemma aeeq_complex_proof {d:ℕ} {f g: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} {hg: ComplexSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) (h_ae: AlmostEverywhereEqual f g) : hf.integ = hg.integ := by
  have hf_re_ai : hf.re.AbsolutelyIntegrable := by
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hf_integ
    have hsub : Support (Complex.re_fun f) ⊆ Support f := by
      intro x hx
      simp only [Support, Set.mem_setOf_eq] at hx ⊢
      intro hzero
      change Complex.re (f x) ≠ 0 at hx
      rw [hzero] at hx
      exact hx (by simp)
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hf_integ
  have hf_im_ai : hf.im.AbsolutelyIntegrable := by
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hf_integ
    have hsub : Support (Complex.im_fun f) ⊆ Support f := by
      intro x hx
      simp only [Support, Set.mem_setOf_eq] at hx ⊢
      intro hzero
      change Complex.im (f x) ≠ 0 at hx
      rw [hzero] at hx
      exact hx (by simp)
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hf_integ
  have hg_re_ai : hg.re.AbsolutelyIntegrable := by
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hg_integ
    have hsub : Support (Complex.re_fun g) ⊆ Support g := by
      intro x hx
      simp only [Support, Set.mem_setOf_eq] at hx ⊢
      intro hzero
      change Complex.re (g x) ≠ 0 at hx
      rw [hzero] at hx
      exact hx (by simp)
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hg_integ
  have hg_im_ai : hg.im.AbsolutelyIntegrable := by
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hg_integ
    have hsub : Support (Complex.im_fun g) ⊆ Support g := by
      intro x hx
      simp only [Support, Set.mem_setOf_eq] at hx ⊢
      intro hzero
      change Complex.im (g x) ≠ 0 at hx
      rw [hzero] at hx
      exact hx (by simp)
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hg_integ
  have h_ae_re : AlmostEverywhereEqual (Complex.re_fun f) (Complex.re_fun g) :=
    AlmostAlways.mp h_ae (fun x hx => by simp [Complex.re_fun, hx])
  have h_re_eq : hf.re.integ = hg.re.integ :=
    RealSimpleFunction.integral_eq_integral_of_aeEqual hf_re_ai hg_re_ai h_ae_re
  have h_ae_im : AlmostEverywhereEqual (Complex.im_fun f) (Complex.im_fun g) :=
    AlmostAlways.mp h_ae (fun x hx => by simp [Complex.im_fun, hx])
  have h_im_eq : hf.im.integ = hg.im.integ :=
    RealSimpleFunction.integral_eq_integral_of_aeEqual hf_im_ai hg_im_ai h_ae_im
  simp [ComplexSimpleFunction.integ, h_re_eq, h_im_eq]

lemma ComplexSimpleFunction.integral_eq_integral_of_aeEqual {d:ℕ} {f g: EuclideanSpace' d → ℂ} {hf: ComplexSimpleFunction f} {hg: ComplexSimpleFunction g} (hf_integ: hf.AbsolutelyIntegrable) (hg_integ: hg.AbsolutelyIntegrable) (h_ae: AlmostEverywhereEqual f g) : hf.integ = hg.integ := by

  have hf_re_ai : hf.re.AbsolutelyIntegrable := by
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hf_integ
    have hsub : Support (Complex.re_fun f) ⊆ Support f := by
      intro x hx
      simp only [Support, Set.mem_setOf_eq] at hx ⊢
      intro hzero
      change Complex.re (f x) ≠ 0 at hx
      rw [hzero] at hx
      exact hx (by simp)
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hf_integ
  have hf_im_ai : hf.im.AbsolutelyIntegrable := by
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hf_integ
    have hsub : Support (Complex.im_fun f) ⊆ Support f := by
      intro x hx
      simp only [Support, Set.mem_setOf_eq] at hx ⊢
      intro hzero
      change Complex.im (f x) ≠ 0 at hx
      rw [hzero] at hx
      exact hx (by simp)
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hf_integ
  have hg_re_ai : hg.re.AbsolutelyIntegrable := by
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hg_integ
    have hsub : Support (Complex.re_fun g) ⊆ Support g := by
      intro x hx
      simp only [Support, Set.mem_setOf_eq] at hx ⊢
      intro hzero
      change Complex.re (g x) ≠ 0 at hx
      rw [hzero] at hx
      exact hx (by simp)
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hg_integ
  have hg_im_ai : hg.im.AbsolutelyIntegrable := by
    rw [RealSimpleFunction.absolutelyIntegrable_iff]
    rw [ComplexSimpleFunction.absolutelyIntegrable_iff] at hg_integ
    have hsub : Support (Complex.im_fun g) ⊆ Support g := by
      intro x hx
      simp only [Support, Set.mem_setOf_eq] at hx ⊢
      intro hzero
      change Complex.im (g x) ≠ 0 at hx
      rw [hzero] at hx
      exact hx (by simp)
    exact lt_of_le_of_lt (Lebesgue_outer_measure.mono hsub) hg_integ
  have h_ae_re : AlmostEverywhereEqual (Complex.re_fun f) (Complex.re_fun g) :=
    AlmostAlways.mp h_ae (fun x hx => by simp [Complex.re_fun, hx])
  have h_re_eq : hf.re.integ = hg.re.integ :=
    RealSimpleFunction.integral_eq_integral_of_aeEqual hf_re_ai hg_re_ai h_ae_re
  have h_ae_im : AlmostEverywhereEqual (Complex.im_fun f) (Complex.im_fun g) :=
    AlmostAlways.mp h_ae (fun x hx => by simp [Complex.im_fun, hx])
  have h_im_eq : hf.im.integ = hg.im.integ :=
    RealSimpleFunction.integral_eq_integral_of_aeEqual hf_im_ai hg_im_ai h_ae_im
  simp [ComplexSimpleFunction.integ, h_re_eq, h_im_eq]

/-- Exercise 1.3.2(iii) (Compatibility with Lebesgue measure, indicator) -/
lemma RealSimpleFunction.indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  RealSimpleFunction (E.indicator') := by
  use 1, (fun _ => (1 : ℝ)), (fun _ => E)
  constructor
  · intro i
    exact hE
  · ext x
    simp

lemma ComplexSimpleFunction.indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) :
  ComplexSimpleFunction (Complex.indicator E) := by
  use 1, (fun _ => (1 : ℂ)), (fun _ => E)
  constructor
  · intro i
    exact hE
  · ext x
    simp [Complex.indicator, Real.complex_fun]

/-- Exercise 1.3.2(iii) (Compatibility with Lebesgue measure) -/


lemma zero_unsigned_integral {d:ℕ} (hf : UnsignedSimpleFunction (fun _ : EuclideanSpace' d => (0 : EReal))) : hf.integ = 0 := by
  rw [UnsignedSimpleFunction.integral_eq hf (k := 0) (c := fun i : Fin 0 => (0 : EReal))
    (E := fun i : Fin 0 => (∅ : Set (EuclideanSpace' d)))
    (hmes := by intro i; fin_cases i) (hnonneg := by intro i; fin_cases i)
    (heq := by ext x; simp)]
  simp

lemma zero_real_integral {d:ℕ} (hf : RealSimpleFunction (fun _ : EuclideanSpace' d => (0 : ℝ))) : hf.integ = 0 := by
  let hzU : UnsignedSimpleFunction (fun _ : EuclideanSpace' d => (0 : EReal)) := by
    use 0, (fun i : Fin 0 => (0 : EReal)), (fun i : Fin 0 => (∅ : Set (EuclideanSpace' d)))
    constructor
    · intro i
      fin_cases i
    · ext x
      simp
  have h_pos_ae : AlmostEverywhereEqual (EReal.pos_fun (fun _ : EuclideanSpace' d => (0 : ℝ)))
      (fun _ : EuclideanSpace' d => (0 : EReal)) :=
    AlmostAlways.ofAlways (fun x => by simp [EReal.pos_fun])
  have h_pos_eq : hf.pos.integ = hzU.integ :=
    UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hf.pos hzU h_pos_ae
  have h_neg_ae : AlmostEverywhereEqual (EReal.neg_fun (fun _ : EuclideanSpace' d => (0 : ℝ)))
      (fun _ : EuclideanSpace' d => (0 : EReal)) :=
    AlmostAlways.ofAlways (fun x => by simp [EReal.neg_fun])
  have h_neg_eq : hf.neg.integ = hzU.integ :=
    UnsignedSimpleFunction.integral_eq_integral_of_aeEqual hf.neg hzU h_neg_ae
  simp [RealSimpleFunction.integ, h_pos_eq, h_neg_eq, zero_unsigned_integral hzU]

lemma RealSimpleFunction.integral_indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (_hfin: Lebesgue_measure E < ⊤): (RealSimpleFunction.indicator hE).integ = (Lebesgue_measure E).toReal := by

  have h_pt : ∀ x, EReal.pos_fun (E.indicator') x = Real.toEReal (E.indicator' x) := by
    intro x
    by_cases hx : x ∈ E
    · simp [EReal.pos_fun, Set.indicator'_of_mem hx]
    · simp [EReal.pos_fun, Set.indicator'_of_notMem hx]
  have h_pos_ae : AlmostEverywhereEqual (EReal.pos_fun (E.indicator')) (Real.toEReal ∘ E.indicator') :=
    AlmostAlways.ofAlways h_pt
  have h_pos_eq : (RealSimpleFunction.indicator hE).pos.integ = (UnsignedSimpleFunction.indicator hE).integ :=
    UnsignedSimpleFunction.integral_eq_integral_of_aeEqual (RealSimpleFunction.indicator hE).pos
      (UnsignedSimpleFunction.indicator hE) h_pos_ae
  have h_pos_val : (RealSimpleFunction.indicator hE).pos.integ = Lebesgue_measure E := by
    rw [h_pos_eq]
    exact UnsignedSimpleFunction.integral_indicator hE
  have h_pt_neg : ∀ x, EReal.neg_fun (E.indicator') x = (0 : EReal) := by
    intro x
    by_cases hx : x ∈ E
    · simp [EReal.neg_fun, Set.indicator'_of_mem hx]
    · simp [EReal.neg_fun, Set.indicator'_of_notMem hx]
  let hzU : UnsignedSimpleFunction (fun _ : EuclideanSpace' d => (0 : EReal)) := by
    use 0, (fun i : Fin 0 => (0 : EReal)), (fun i : Fin 0 => (∅ : Set (EuclideanSpace' d)))
    constructor
    · intro i
      fin_cases i
    · ext x
      simp
  have h_neg_ae : AlmostEverywhereEqual (EReal.neg_fun (E.indicator'))
      (fun _ : EuclideanSpace' d => (0 : EReal)) :=
    AlmostAlways.ofAlways h_pt_neg
  have h_neg_eq : (RealSimpleFunction.indicator hE).neg.integ = hzU.integ :=
    UnsignedSimpleFunction.integral_eq_integral_of_aeEqual (RealSimpleFunction.indicator hE).neg hzU h_neg_ae
  have h_neg_val : (RealSimpleFunction.indicator hE).neg.integ = 0 := by
    rw [h_neg_eq]
    exact zero_unsigned_integral hzU
  simp [RealSimpleFunction.integ, h_pos_val, h_neg_val]

lemma ComplexSimpleFunction.integral_indicator {d:ℕ} {E: Set (EuclideanSpace' d)} (hE: LebesgueMeasurable E) (hfin: Lebesgue_measure E < ⊤): (ComplexSimpleFunction.indicator hE).integ = (Lebesgue_measure E).toReal := by

  have h_pt_re : ∀ x, Complex.re_fun (Complex.indicator E) x = E.indicator' x := by
    intro x
    by_cases hx : x ∈ E
    · simp [Complex.re_fun, Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hx]
    · simp [Complex.re_fun, Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx]
  have h_pt_im : ∀ x, Complex.im_fun (Complex.indicator E) x = 0 := by
    intro x
    by_cases hx : x ∈ E
    · simp [Complex.im_fun, Complex.indicator, Real.complex_fun, Set.indicator'_of_mem hx]
    · simp [Complex.im_fun, Complex.indicator, Real.complex_fun, Set.indicator'_of_notMem hx]
  have h_re_pt : Complex.re_fun (Complex.indicator E) = E.indicator' := by
    funext x
    exact h_pt_re x
  have h_re_eq : (ComplexSimpleFunction.indicator hE).re.integ = (RealSimpleFunction.indicator hE).integ :=
    integ_eq_of_fun_eq h_re_pt
  have h_re_val : (ComplexSimpleFunction.indicator hE).re.integ = (Lebesgue_measure E).toReal := by
    rw [h_re_eq]
    exact RealSimpleFunction.integral_indicator hE hfin
  let hzR : RealSimpleFunction (fun _ : EuclideanSpace' d => (0 : ℝ)) := by
    use 0, (fun i : Fin 0 => (0 : ℝ)), (fun i : Fin 0 => (∅ : Set (EuclideanSpace' d)))
    constructor
    · intro i
      fin_cases i
    · ext x
      simp
  have h_im_pt : Complex.im_fun (Complex.indicator E) = (fun _ : EuclideanSpace' d => (0 : ℝ)) := by
    funext x
    exact h_pt_im x
  have h_im_eq : (ComplexSimpleFunction.indicator hE).im.integ = hzR.integ :=
    integ_eq_of_fun_eq h_im_pt
  have h_im_val : (ComplexSimpleFunction.indicator hE).im.integ = 0 := by
    rw [h_im_eq]
    exact zero_real_integral hzR
  simp [ComplexSimpleFunction.integ, h_re_val, h_im_val]
