# `Rat.instField` —— 自定义有理数的域结构

## `Field` 是什么

在抽象代数中，**域 (Field)** 是一个配备了加法、乘法、减法、除法（除以非零元）的代数结构，满足：
- 加法构成交换群 (Abelian group)
- 乘法构成交换群（去掉 0）
- 分配律

Lean 的 `Field` 类型类封装了这些性质，包含大量字段（fields，也可理解为"要填的槽"）：

```
Field K 需要提供（或自动派生）：
├── toCommRing       ← 已由 instCommRing 提供
├── toInv            ← 已由 instInv 提供
├── toDiv            ← 由 DivInvMonoid 默认提供
├── div_eq_mul_inv   ← 默认 a / b = a * b⁻¹
├── zpow / zpow_zero' / zpow_succ' / zpow_neg'  ← DivInvMonoid 默认
├── toNontrivial     ← exists_pair_ne（存在两个不同元素）
├── toRatCast        ← 已由 instRatCast 提供 (ℚ → Rat)
├── toNNRatCast      ← 我们新加的 (ℚ≥0 → Rat)
├── mul_inv_cancel   ← x ≠ 0 → x * x⁻¹ = 1
├── inv_zero         ← 0⁻¹ = 0（junk value）
├── ratCast_def      ← (q : Rat) = q.num / q.den
├── nnratCast_def    ← 同上，对 ℚ≥0
├── qsmul / qsmul_def       ← ℚ 对标量乘法
└── nnqsmul / nnqsmul_def   ← ℚ≥0 对标量乘法
```

## 各个定理的证明

### `exists_pair_ne` — 存在两个不同元素

```lean4
refine ⟨0, 1, ?_⟩
intro h
have := ((Rat.eq (0 : ℤ) (1 : ℤ) h1 h1).mp h)
norm_num at this
```

要证明 `0 ≠ 1`，反证法：假设相等 → 用 `Rat.eq` 转为整数等式 `0*1 = 1*1` → `norm_num` 发现矛盾。

### `mul_inv_cancel` — 非零元乘以逆等于 1

```lean4
intro x hx0
obtain ⟨a, b, hb, rfl⟩ := Rat.eq_diff x
have ha : a ≠ 0 := ...
```

证明链：
1. 把 `x` 写成 `a // b`（`a ≠ 0` 因为 `x ≠ 0`）
2. `(a//b)⁻¹ = b//a`（`inv_eq` 引理）
3. `(a//b) * (b//a) = (a*b) // (b*a)`（`mul_eq`）
4. `= (a*b) // (a*b)`（交换律）
5. `= 1 // 1 = 1`（`Rat.eq` + `simp`）

### `inv_zero` — 0⁻¹ = 0

```lean4
rfl
```

因为我们定义的 `inv` 把 `0` 的逆赋值为 `0`（junk value）。

### `ratCast_def` — ℚ 到 Rat 的转换

```lean4
calc
  (q : Rat) = q.num // q.den := rfl           -- RatCast 的定义
  _ = (q.num // 1) * (1 // q.den) := ...       -- mul_eq
  _ = (q.num : Rat) * ((q.den : Rat)⁻¹) := ... -- coe_Int_eq, coe_Nat_eq, inv_eq
  _ = (q.num : Rat) / (q.den : Rat) := rfl     -- 除法的定义
```

### `qsmul` / `nnqsmul` — 对标量乘法

```lean4
qsmul := (fun a x => (a : Rat) * x)      -- ℚ 作用在 Rat 上
qsmul_def := by intro a x; rfl

nnqsmul := (fun a x => ((a : ℚ) : Rat) * x)  -- ℚ≥0 先转 ℚ 再转 Rat
nnqsmul_def := by intro a x; rfl
```

标量乘法直接定义为域乘法。`ℚ≥0` 没有直接到 `Rat` 的 coercion，所以先经过 `ℚ`。

### `nnratCast_def` — ℚ≥0 到 Rat 的转换

通过 `NNRat.num_coe / NNRat.den_coe` 引理，归约到 `ratCast_def` 的相同证明模式。

## 自定义 Rat vs ℚ 的桥接

| 路径 | 方式 |
|------|------|
| `ℚ → Rat` | `instRatCast`：`q.num // q.den` |
| `ℚ≥0 → Rat` | `instNNRatCast`：`(q : ℚ) : Rat` |
| 单射性 | `ratCast_inj`：`(n:Rat) = (m:Rat) → n = m` |
| 兼容性 | `coe_Rat_eq`：`(a/b : ℚ) = a // b` |
