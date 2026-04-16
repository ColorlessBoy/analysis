# Example 3.6.3 证明详解：类型转化链条

## 目标

**自然语言**：证明偶数集和自然数集等势（存在双射 `n ↦ 2n`）。

**Lean 形式化**：

```lean
theorem SetTheory.Set.Example_3_6_3 : 
  EqualCard nat (nat.specify (fun x ↦ Even (x:ℕ))) := by ...
```

`EqualCard X Y` 定义为存在双射 `f : X → Y`。

---

## 类型解剖：两端是什么类型？

这是证明中最"不平凡"的部分——证明两端的类型不是直觉上的 `ℕ`，而是两组嵌套的 **subtype**。

### 左侧：nat

```lean
nat.toSubtype   -- = Subtype (fun x ↦ x ∈ nat)
```

`SetTheory.Set` 中的 `nat` 是一个集合（Axiom 3.8），`toSubtype` 把集合转化为一个 `Subtype`：

```lean
abbrev SetTheory.Set.toSubtype (A:Set) := Subtype (fun x ↦ x ∈ A)
```

### 右侧：nat.specify (Even · ℕ)

```lean
nat.specify (fun x ↦ Even (x:ℕ))   -- 从 nat 中挑出满足 Even 条件的元素，形成子集
(nat.specify ...).toSubtype        -- 该子集对应的 subtype
```

`specify` 对应集合论中的**限制（specification / separation）公理**：

```lean
theorem specification_axiom'' {A:Set} (P: A → Prop) (x:Object) :
    x ∈ A.specify P ↔ ∃ h:x ∈ A, P ⟨ x, h ⟩
```

### 关键桥梁：nat_equiv

Axiom 3.8 声明：

```lean
nat_equiv : ℕ ≃ Subtype (mem . nat)   -- Equiv 类型间的双射
```

即 `nat_equiv : ℕ ≃ nat.toSubtype`。这意味着：
- `nat.toSubtype` 在作为类型使用时，本质上就是 `ℕ`（有一个显式的 equivalence）
- 可以在 `ℕ` 和 `nat.toSubtype` 之间来回转换而不丢信息

---

## 目标双射的构造

### 直观想法

`f : ℕ → 偶数集`，`f(n) = 2n`

### Lean 中的具体构造

```lean
let f : nat.toSubtype → (nat.specify (fun x ↦ Even (x:ℕ))).toSubtype := fun x =>
  let n : ℕ := nat_equiv.symm x              -- x : nat.toSubtype → ℕ
  let two_n_nat : nat.toSubtype := nat_equiv (2 * n)  -- ℕ → nat.toSubtype
  ⟨two_n_nat.val, by                           -- 打包成 .toSubtype 的元素
    rw [specification_axiom'']
    refine ⟨two_n_nat.property, ?_⟩           -- two_n_nat.val ∈ nat 且是偶数
    show Even (nat_equiv.symm ⟨two_n_nat.val, two_n_nat.property⟩)
    simp [two_n_nat]⟩
```

### 逐行类型追踪

```
x : nat.toSubtype
  └── 实际是 {x : Object // x ∈ nat}，但 nat_equiv 把它等价于 ℕ

nat_equiv.symm x : ℕ
  └── 将集合论的自然数元素转化为 Lean 的 ℕ 类型

nat_equiv (2 * n) : nat.toSubtype
  └── 把 ℕ 类型的 2n 再转回 nat.toSubtype（即集合中的偶数）

⟨two_n_nat.val, ...⟩ : (nat.specify ...).toSubtype
  └── 打包成偶数子集的 subtype 元素
```

---

## 证明的三个层次

### 第一层：injective（单射）

**目标**：`f x1 = f x2 → x1 = x2`

```lean
intro x1 x2 h
have hval : (f x1).val = (f x2).val := congrArg Subtype.val h
simp only [f] at hval
have hval2 : nat_equiv (2 * nat_equiv.symm x1) = nat_equiv (2 * nat_equiv.symm x2) :=
  Subtype.val_injective hval
have hval3 : 2 * nat_equiv.symm x1 = 2 * nat_equiv.symm x2 := nat_equiv.injective hval2
have hval4 : nat_equiv.symm x1 = nat_equiv.symm x2 := by omega
exact nat_equiv.symm.injective hval4
```

#### 使用的类型转化定理清单

| 定理 | 内容 | 作用 |
|------|------|------|
| `congrArg Subtype.val h` | 从 `f x1 = f x2` 提取 `.val` 部分 | 丢弃证明，只留数值相等 |
| `Subtype.val_injective` | Subtype 的 `.val` 映射是单射 | 从 `⟨a,ha⟩ = ⟨b,hb⟩` 得到 `a = b` |
| `nat_equiv.injective` | `nat_equiv : ℕ ≃ nat.toSubtype` 是双射 | 去掉 `nat_equiv`，得到 `2*symm x1 = 2*symm x2` |
| `nat_equiv.symm.injective` | 等价映射的逆也是单射 | 得到 `symm x1 = symm x2` |
| `omega` | 算术消去：乘法相同则原数相同 | `2*a = 2*b → a = b`（在 ℕ 上） |

**类型转化链**：

```
f x1 = f x2
  ↓ congrArg Subtype.val
(two_n_nat.val at x1) = (two_n_nat.val at x2)
  ↓ Subtype.val_injective（已知）
nat_equiv (2 * symm x1) = nat_equiv (2 * symm x2)
  ↓ nat_equiv.injective（因为是 Equiv）
2 * symm x1 = 2 * symm x2
  ↓ omega
symm x1 = symm x2
  ↓ nat_equiv.symm.injective
x1 = x2
```

---

### 第二层：surjective（满射）

**目标**：对每个 `y : (nat.specify ...).toSubtype`，找到 `x` 使 `f x = y`

```lean
intro y
have hy_spec := y.property
rw [specification_axiom''] at hy_spec    -- y.val ∈ nat.specify P → ∃ h, P ⟨h⟩  ... 
obtain ⟨hy_mem, hy_even⟩ := hy_spec      -- hy_mem : y.val ∈ nat, hy_even : Even y.val
obtain ⟨k, hk⟩ := hy_even                 -- hk : y.val = 2 * k
use nat_equiv k
apply Subtype.ext
simp only [f, Equiv.symm_apply_apply]
have : nat_equiv (k + k) = ⟨y.val, hy_mem⟩ := by
  apply nat_equiv.symm.injective; simp [hk]
rw [show 2 * k = k + k from by ring]
exact congrArg Subtype.val this
```

#### 使用的类型转化定理清单

| 定理 | 内容 | 作用 |
|------|------|------|
| `specification_axiom''` | `x ∈ A.specify P ↔ ∃ h:x∈A, P ⟨x,h⟩` | 把 `y.property` 展开为集合成员+偶数条件 |
| `Equiv.symm_apply_apply` | `nat_equiv.symm (nat_equiv k) = k` | 简化 `f (nat_equiv k)` 中出现的关键项 |
| `nat_equiv.symm.injective` | `symm a = symm b → a = b` | 从 `nat_equiv (k+k) = ⟨y.val,hy_mem⟩` 推出 `k+k = y.val`（在 ℕ 层面） |
| `congrArg Subtype.val` | 把等式应用到 `.val` 投影 | 最终证明 `two_n_nat.val = y.val` |
| `Subtype.ext` | `⟨a,ha⟩ = ⟨b,hb⟩ ↔ a = b`（当 ha = hb 可证明时） | 综合数值相等和性质相等 |

**类型转化链**：

```
y : (nat.specify ...).toSubtype
  ↓ y.property（拆出 .val 和 .property）
hy_mem : y.val ∈ nat
hy_even : Even y.val
  ↓ hy_even（因为 Even y.val ↔ ∃ k, y.val = 2*k）
hk : y.val = 2 * k
  ↓ use nat_equiv k
x = nat_equiv k : nat.toSubtype
  ↓ f x 展开
⟨nat_equiv (2*k).val, ...⟩ = ⟨y.val, hy_mem⟩   -- 目标
  ↓ Equiv.symm_apply_apply
⟨nat_equiv (2*k).val, ...⟩ = ⟨nat_equiv (k+k).val, ...⟩
  ↓ nat_equiv.symm.injective
2*k = k+k   -- 由 omega
```

---

## 核心类型转化操作图

```
              ℕ                              ℕ
              ↑ nat_equiv                    ↑ nat_equiv
              │                              │
    nat.toSubtype ←───── nat_equiv.symm ─── nat.toSubtype
              │                              │
              │ two_n_nat.val                │ y.val
              ↓                              ↓
      Even val? ─────────────────────── y.val (已验证是偶数)
              │
              ↓ specification_axiom''
      (nat.specify ...).toSubtype
```

---

## 辅助引理速查

| 引理 | 文件位置 | 用途 |
|------|----------|------|
| `nat_equiv : ℕ ≃ nat.toSubtype` | Section_3_1.lean:100（公理） | ℕ 与集合论自然数双射 |
| `nat_equiv.injective` | 来自 `Equiv.bijective` | 等价映射正向单射 |
| `nat_equiv.symm.injective` | 来自 `Equiv.bijective` | 等价映射逆向单射 |
| `Equiv.apply_eq_iff_eq` | Mathlib `Equiv` | `Equiv a = Equiv b ↔ a = b` |
| `Equiv.symm_apply_apply` | Mathlib `Equiv` | `s (s⁻¹ x) = x` |
| `Subtype.val_injective` | Mathlib `Subtype` | subtype 投影单射 |
| `Subtype.ext` | Mathlib `Subtype` | Extensionality for subtypes |
| `specification_axiom''` | Section_3_1.lean:510 | 限制公理（第二形式） |

---

## 为什么自然语言证明"平凡无趣"？

在数学上，"ℕ 和偶数集等势"几乎是一句话：

> 双射 `n ↦ 2n` 显然是一个双射。

但在 Lean 4 形式化中，这句话被翻译成证明时，需要处理**三重类型系统鸿沟**：

1. **ℕ**（Lean 的 `ℕ` 类型）
2. **nat**（集合论 `SetTheory.Set` 中的集合）
3. **nat.toSubtype**（集合的 subtype 形式）
4. **nat.specify ...**（子集）
5. **nat.specify ....toSubtype**（子集的 subtype 形式）

每一步 `nat_equiv`、`nat_equiv.symm`、`specification_axiom''` 的调用都是在**跨越这些类型层面的鸿沟**。这正是这段证明"琐碎但复杂"的根本原因——不是数学难，而是类型体操难。
