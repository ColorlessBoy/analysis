# Section_4_2.Rat vs ℚ  —— 自定义有理数与 Mathlib 标准有理数

## 两个不同的 `Rat`

| 名称 | 定义 | 本质 |
|------|------|------|
| `Section_4_2.Rat` | `abbrev Rat := Quotient PreRat.instSetoid` | 按教材构造的**商类型**：`PreRat`（分子 `ℤ` × 分母 `ℤ`，分母 ≠ 0）在等价关系 `a*d = c*b` 下的商 |
| `ℚ` (即 `_root_.Rat`) | Mathlib 内置有理数 | **结构体**：`num : ℤ`，`den : ℕ`，`den_nz`，`reduced`（已约简） |

两者是完全不同的类型，都叫 `Rat`，但 `Section_4_2.Rat` 在 `Section_4_2` 命名空间下。

## 三个关键定义

### 1. `Rat.instRatCast` — 注册类型转换

```lean4
instance Rat.instRatCast : RatCast Rat where
  ratCast q := q.num // q.den
```

给自定义 `Rat` 注册 `RatCast`，使得 `(q : Rat)` 可以把 Mathlib 的 `q : ℚ` 转换为自定义 `Rat`：取 `q.num : ℤ` 和 `q.den : ℕ`，用 `//` 构造自定义有理数。

### 2. `Rat.ratCast_inj` — 证明转换是单射

```lean4
theorem Rat.ratCast_inj : Function.Injective (fun n:ℚ ↦ (n:Rat)) := ...
```

证明：如果 `(n : Rat) = (m : Rat)`（自定义有理数相等），则 `n = m`（Mathlib 有理数相等）。

证明链：
- `(n : Rat)` 展开为 `n.num // n.den`
- 自定义 `//` 的相等判据 `Rat.eq`：`a//b = c//d ↔ a*d = c*b`
- 于是 `n.num // n.den = m.num // m.den` 等价于 `n.num * m.den = m.num * n.den`
- Mathlib 的 `Rat.eq_iff_mul_eq_mul`：`n = m ↔ n.num * m.den = m.num * n.den`
- 等式成立

这确保了自定义有理数和 Mathlib 有理数之间有**忠实的嵌入**。

### 3. `Rat.coe_Rat_eq` — 与整数除法兼容

```lean4
theorem Rat.coe_Rat_eq (a:ℤ) {b:ℤ} (hb: b ≠ 0) : (a/b:ℚ) = a // b := ...
```

对整数 `a, b`（`b ≠ 0`），Mathlib 的除法 `a/b : ℚ` 转换到自定义 `Rat` 后等于直接用 `//` 构造的 `a // b`。

## 总结

| 概念 | 含义 |
|------|------|
| `Section_4_2.Rat` | 按陶哲轩 Chapter 4.2，用 `ℤ×ℤ/∼` 构造的有理数 |
| `ℚ` (`_root_.Rat`) | Mathlib 标准有理数（约简后结构体） |
| `RatCast` 桥 | `instRatCast` 定义 `ℚ → Section_4_2.Rat` 的映射 |
| `ratCast_inj` | 证明该映射是单射（嵌入） |
| `coe_Rat_eq` | 证明该映射与 `//` 在整数除法上兼容 |

构造自定义 `Rat` 的目的是 faithful 翻译教材构造过程；最后通过 `RatCast` 桥接到 Mathlib 的 `ℚ`，使后续章节可以直接用标准有理数。
