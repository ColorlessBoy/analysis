# Setoid 详解

## 什么是 Setoid？

Setoid 是一个**附有等价关系**的类型。在 Lean 4 的类型论中，它是构造**商类型（Quotient Type）**的基础设施。

```lean
class Setoid (α : Sort u) where
  r : α → α → Prop        -- 等价关系
  iseqv : Equivalence r   -- 自反、对称、传递
```

即：`Setoid α` = 类型 α + 等价关系 `≈`（记作 `r`）+ 证明 `r` 是等价关系。

> **核心直觉**：Setoid 让我们可以把"相等"这个默认的 identity relation `=` 替换成任意满足自反、对称、传递的关系，从而在商类型中把"不同代表元"视为"同一个对象"。

---

## 公理与定理全表

### 1. Setoid 类型类自身

| 名称 | 类型 | 说明 |
|------|------|------|
| `Setoid.r` | `α → α → Prop` | 等价关系，也写作 `≈` |
| `Setoid.iseqv` | `Equivalence r` | `r` 是自反、对称、传递的 |

### 2. Setoid 命名空间下的三条基本定理

| 名称 | 声明 | 内容 |
|------|------|------|
| `Setoid.refl` | `{a : α} → a ≈ a` | 自反性 |
| `Setoid.symm` | `{a b : α} → a ≈ b → b ≈ a` | 对称性 |
| `Setoid.trans` | `{a b c : α} → a ≈ b → b ≈ c → a ≈ c` | 传递性 |

```lean
namespace Setoid
variable {α : Sort u} [Setoid α]

theorem refl (a : α) : a ≈ a := iseqv.refl a
theorem symm {a b : α} (hab : a ≈ b) : b ≈ a := iseqv.symm hab
theorem trans {a b c : α} (hab : a ≈ b) (hbc : b ≈ c) : a ≈ c := iseqv.trans hab hbc
end Setoid
```

### 3. HasEquiv 实例——`≈` 记号

```lean
instance {α : Sort u} [Setoid α] : HasEquiv α := ⟨Setoid.r⟩
```

一旦为某类型声明了 `Setoid` 实例，该类型就自动获得 `≈` 记号，等价于 `Setoid.r`：
- `a ≈ b` = `@HasEquiv.Equiv α _ a b` = `Setoid.r a b`

### 4. Quotient（商类型）与 Quotient.mk

`Quotient s` 是基于 Setoid `s` 构建的商类型，`Quotient.mk s a` 将 `a : α` 映射到它的等价类。

```lean
def Quotient {α : Sort u} (s : Setoid α) := @Quot α Setoid.r
def Quotient.mk {α : Sort u} (s : Setoid α) (a : α) : Quotient s := Quot.mk Setoid.r a
```

#### Quotient 的核心定理

| 名称 | 声明 | 内容 |
|------|------|------|
| `Quotient.sound` | `{a b : α} → a ≈ b → ⟦a⟧ = ⟦b⟧` | 等价推出商相等（正向） |
| `Quotient.exact` | `{a b : α} → ⟦a⟧ = ⟦b⟧ → a ≈ b` | 商相等推出等价（反向） |
| `Quotient.ind` | `{motive : Quotient s → Prop} → ((a : α) → motive ⟦a⟧) → (q : Quotient s) → motive q` | 归纳原理 |
| `Quotient.lift` | `{f : α → β} → ((a b : α) → a ≈ b → f a = f b) → Quotient s → β` | 提升函数到商 |
| `Quotient.liftOn` | `q : Quotient s → (f : α → β) → ((a b : α) → a ≈ b → f a = f b) → β` | 带参数提升 |
| `Quotient.exists_rep` | `(q : Quotient s) → ∃ a, ⟦a⟧ = q` | 每个商元素都有代表元 |
| `Quotient.rec` | 递归子（带修正项 `h`） | 高阶递归 |
| `Quotient.recOn` | 对商参数使用递归 | 递归在参数上 |
| `Quotient.decidableEq` | （需等价关系可判定了）| 商上相等性可判定 |

> **sound + exact** 给出等价判定：
> ```lean
> ⟦a⟧ = ⟦b⟧ ↔ a ≈ b    -- 这是 Quotient 的核心性质
> ```

### 5. Quotient.lift —— 如何在商上定义函数

这是 Setoid 最重要的应用模式。分两步：

1. **验证**函数 `f : α → β` **保持等价关系**（compatible）：
   ```lean
   (a b : α) → a ≈ b → f a = f b
   ```
2. **提升**到商上：
   ```lean
   Quotient.lift f hf : Quotient s → β
   -- 且满足：lift f hf ⟦a⟧ = f a
   ```

### 6. Quotient.lift₂ —— 二元函数的双重提升

```lean
Quotient.lift₂ (f : α → β → φ)
  (c : (a₁ : α) → (b₁ : β) → (a₂ : α) → (b₂ : β) → a₁ ≈ a₂ → b₁ ≈ b₂ → f a₁ b₁ = f a₂ b₂)
  (q₁ : Quotient s₁) (q₂ : Quotient s₂) : φ
```

### 7. Quotient.recOn / recOnSubsingleton

用于对商参数做模式匹配/归纳，其中 `recOnSubsingleton` 在 motive 的每个子类都是单例时特别有用（如 `DecidableEq` 场景）。

---

## 依赖关系图

```
Equivalence（自反、对称、传递）
    │
    └── 被 Setoid.iseqv 引用
            │
            └── Setoid (类型类：α + 等价关系)
                    │
                    ├── Setoid.refl / .symm / .trans
                    │
                    └── 用于构造 Quotient（商类型）
                            │
                            ├── Quotient.mk（商映射）
                            │       │
                            │       ├── Quotient.sound（等价 → 商相等）
                            │       └── Quotient.exact（商相等 → 等价）
                            │
                            ├── Quotient.lift（提升函数）
                            │       └── 前提：f 保持等价关系
                            │
                            ├── Quotient.ind（归纳）
                            ├── Quotient.liftOn
                            ├── Quotient.lift₂（二元）
                            ├── Quotient.rec / recOn
                            └── Quotient.exists_rep
```

---

## 项目中的实际例子

### 例 1：PreInt —— 整数形式差分构造

文件：[analysis/Section_4_1.lean:40](analysis/Section_4_1.lean#L40)

```lean
instance PreInt.instSetoid : Setoid PreInt where
  r a b := a.minuend + b.subtrahend = b.minuend + a.subtrahend
  iseqv := { refl := by sorry, symm := by sorry, trans := by sorry }

abbrev Int := Quotient PreInt.instSetoid
```

整数 `a —— b` 被定义为自然数对 `(a, b)` 的商， equivalence：`a + d = c + b ↔ (a,b) ≈ (c,d)`。

关键性质：
```lean
-- Int.eq_diff：每个整数都有 a —— b 形式
theorem Int.eq_diff (n:Int) : ∃ a b, n = a —— b

-- 定义加法时用 lift 提升
instance Int.instAdd : Add Int where
  add := Quotient.lift₂ (fun ⟨a,b⟩ ⟨c,d⟩ ↦ (a+c)——(b+d))
    (by intro ...; simp [eq] at *; omega)
```

---

### 例 2：PreRat —— 有理数形式商构造

文件：[analysis/Section_4_2.lean:47](analysis/Section_4_2.lean#L47)

```lean
instance PreRat.instSetoid : Setoid PreRat where
  r a b := a.numerator * b.denominator = b.numerator * a.denominator
  iseqv := { refl := by sorry, symm := by sorry, trans := by sorry }

abbrev Rat := Quotient PreRat.instSetoid
abbrev Rat.formalDiv (a b:ℤ) : Rat :=
  Quotient.mk PreRat.instSetoid (if h:b ≠ 0 then ⟨a,b,h⟩ else ⟨0,1,by decide⟩)
```

等价关系：`a/b ≈ c/d ↔ a·d = c·b`（交叉相乘相等）。

相等性判定用到了 `Quotient.eq`（即 `Quotient.sound/exact` 的结合）：
```lean
theorem Rat.eq (a c:ℤ) {b d:ℤ} (hb: b ≠ 0) (hd: d ≠ 0):
    a // b = c // d ↔ a * d = c * b := by
  simp [formalDiv, hb, hd, Quotient.eq, PreRat.instSetoid]
  --                ^^^^^^^^^^^^^^^^ 使用 Quotient.mk a = Quotient.mk b ↔ a ≈ b
```

---

### 例 3：CauchySequence —— 实数构造

文件：[analysis/Section_5_3.lean:71](analysis/Section_5_3.lean#L71)

```lean
instance CauchySequence.instSetoid : Setoid CauchySequence where
  r := fun a b ↦ Sequence.Equiv a b
  iseqv := { refl := sorry, symm := sorry, trans := sorry }

abbrev Real := Quotient CauchySequence.instSetoid
```

柯西序列等价：`a ≈ b ↔ ∀ ε > 0, ∃ N, ∀ m,n ≥ N, |a_m - b_m| < ε`。

---

### 例 4：Section_3_6 —— EqualCard 等势关系

文件：[analysis/Section_3_6.lean:130](analysis/Section_3_6.lean#L130)

```lean
instance SetTheory.Set.EqualCard.inst_setoid : Setoid SetTheory.Set := 
  ⟨ EqualCard, {refl, symm, trans} ⟩
```

`EqualCard X Y := ∃ f : X → Y, Function.Bijective f`（双射存在）构成集合间的等价关系。

另外在 [Section_8_1.lean:48](analysis/Section_8_1.lean#L48)：
```lean
instance EqualCard.instSetoid : Setoid Type := ⟨ EqualCard, ⟨ refl, symm, trans ⟩ ⟩
```

---

### 例 5：相等性即等价关系

文件：[analysis/Appendix_A_7.lean:49](analysis/Appendix_A_7.lean#L49)

```lean
def equality_as_equiv_relation (X:Type) : Setoid X := {
  r a b := a = b
  iseqv := { refl := Eq.refl, symm := Eq.symm, trans := Eq.trans }
}
```

平凡情况：把普通的相等关系 `=` 包装成 Setoid。这是 `Quotient` 最基础的实例。

---

### 例 6：测度论中的几乎处处相等

文件：[analysis/MeasureTheory/Section_1_2_2.lean:1775](analysis/MeasureTheory/Section_1_2_2.lean#L1775)

```lean
instance IsElementary.ae_equiv {d:ℕ} {A: Set (EuclideanSpace' d)} (hA: IsElementary A):
  Setoid (Set A) := {
  r E F := IsNull (Subtype.val '' symmDiff E F)
  iseqv := by sorry
}
```

两集合等价当且仅当它们的对称差是零测集。这是测度论中"几乎处处相等"的形式化。

---

## Setoid 与 Mathlib 标准库的关系

| 概念 | 本项目 | Mathlib 对应 |
|------|--------|-------------|
| 等价关系 | `Setoid.r`（`≈`） | `HasEquiv.Equiv` |
| 商类型 | `Quotient s` | 相同 |
| 整数构造 | `Section_4_1.Int` | `_root_.Int`（后续使用） |
| 有理数构造 | `Section_4_2.Rat` | `_root_.Rat`（后续使用） |
| 实数构造 | `Chapter5.Real` | `_root_.Real`（后续使用） |
| 等势关系 | `SetTheory.Set.EqualCard` | `Equiv` / `Cardinal.mk` |

---

## 核心设计模式总结

```
构造商类型的三步曲：

Step 1  定义原始类型（ scaffolding type ）
  例：PreInt = ℕ × ℕ（ minuend / subtrahend ）

Step 2  定义 Setoid 实例（给原始类型装备等价关系）
  例：⟨a,b⟩ ≈ ⟨c,d⟩ ↔ a+d = c+b

Step 3  用 Quotient 构造商（抹平等价类）
  例：abbrev Int := Quotient PreInt.instSetoid

Step 4  用 Quotient.lift / lift₂ 定义运算（必须验证 compatibility）
  例：+ : Int → Int → Int := Quotient.lift₂ (fun ... → ...) (by sorry)
```

---

## 常见错误与注意事项

1. **忘记验证 compatibility**：在 `lift` 或 `lift₂` 中必须提供证明说明函数保持等价关系，否则 `Quotient.lift` 的前提不满足。

2. **`≈` 与 `=` 的混淆**：`a ≈ b` 是 Setoid 中的等价关系，`⟦a⟧ = ⟦b⟧` 是商中的相等性。`Quotient.sound` 沟通两者：`a ≈ b → ⟦a⟧ = ⟦b⟧`。

3. **在 `simp` 中使用 `Quotient.eq`**：`Quotient.eq`（即 `exact`）把商相等转化为等价关系，是 `simp` 列表中的重要一环（见 `Section_4_2.lean:69`）。

4. **` Quotient.recOnSubsingleton`**：当 motive 的每个值都是 `Subsingleton` 时（如证明 `DecidableEq`），使用此变体可避免额外的 compatibility 证明。

5. **类型类推理**：当使用 `Quotient.mk'`（省略 Setoid 参数）时，需要类型类能找到对应的 `Setoid` 实例。
