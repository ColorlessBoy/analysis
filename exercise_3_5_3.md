# Exercise 3.5.3

## 题目说明

本节练习的目标是避免直接 rewrite（那样会让所有结论都变得 trivial），而是使用 `OrderedPair.eq` 或 `SetTheory.Set.tuple_inj` 来建立等式的传递性、对称性和自反性。

## 题目与解答

### OrderedPair 的三条

```lean
theorem OrderedPair.refl (p: OrderedPair) : p = p := by
  exact (OrderedPair.eq p.fst p.snd p.fst p.snd).mpr ⟨rfl, rfl⟩

theorem OrderedPair.symm (p q: OrderedPair) : p = q ↔ q = p := by
  constructor
  · intro h
    rw [OrderedPair.eq] at h
    have : p.fst = q.fst ∧ p.snd = q.snd := h
    have : q.fst = p.fst ∧ q.snd = p.snd := ⟨this.1.symm, this.2.symm⟩
    exact (OrderedPair.eq q.fst q.snd p.fst p.snd).mpr this
  · intro h
    rw [OrderedPair.eq] at h
    have : q.fst = p.fst ∧ q.snd = p.snd := h
    have : p.fst = q.fst ∧ p.snd = q.snd := ⟨this.1.symm, this.2.symm⟩
    exact (OrderedPair.eq p.fst p.snd q.fst q.snd).mpr this

theorem OrderedPair.trans {p q r: OrderedPair} (hpq: p=q) (hqr: q=r) : p=r := by
  rw [OrderedPair.eq] at hpq hqr
  exact (OrderedPair.eq p.fst p.snd r.fst r.snd).mpr
    ⟨hpq.1.trans hqr.1, hpq.2.trans hqr.2⟩
```

**分析：**

- `refl`：用 `(OrderedPair.eq p.fst p.snd p.fst p.snd).mpr ⟨rfl, rfl⟩` 构造，通过 `OrderedPair.eq` 将 `p = p` 等价于 `p.fst = p.fst ∧ p.snd = p.snd`，再各用 `rfl` 证明后组合回去。
- `symm`：先将 `h : p = q` 用 `OrderedPair.eq` 展开为 `p.fst = q.fst ∧ p.snd = q.snd`，再用 `⟨h.1.symm, h.2.symm⟩` 交换两个分量，最后用 `(OrderedPair.eq ...).mpr` 重新组合成 `q = p`。两个方向完全对称。
- `trans`：先将 `hpq` 和 `hqr` 用 `OrderedPair.eq` 展开，然后对各分量用 `Eq.trans` 传递，最后用 `(OrderedPair.eq ...).mpr` 组合回去。

---

### tuple 的三条

```lean
theorem SetTheory.Set.tuple_refl {I:Set} {X: I → Set} (a: ∀ i, X i) :
    tuple a = tuple a := (tuple_inj a a).mpr (Eq.refl a)

theorem SetTheory.Set.tuple_symm {I:Set} {X: I → Set} (a b: ∀ i, X i) :
    tuple a = tuple b ↔ tuple b = tuple a :=
  ⟨fun h ↦ (tuple_inj b a).mpr (Eq.symm ((tuple_inj a b).mp h)),
   fun h ↦ (tuple_inj a b).mpr (Eq.symm ((tuple_inj b a).mp h))⟩

theorem SetTheory.Set.tuple_trans {I:Set} {X: I → Set} {a b c: ∀ i, X i}
  (hab: tuple a = tuple b) (hbc : tuple b = tuple c) :
    tuple a = tuple c := by
  have hab' := (tuple_inj a b).mp hab
  have hbc' := (tuple_inj b c).mp hbc
  exact (tuple_inj a c).mpr (hab'.trans hbc')
```

**分析：**

- 关键引理 `tuple_inj`：`tuple a = tuple b ↔ a = b`，建立了 tuple 层面和 function 层面之间的等价。
- `refl`：用 `(tuple_inj a a).mpr (Eq.refl a)` 构造。先用 `tuple_inj a a` 得到 `tuple a = tuple a ↔ a = a`，再用 `Eq.refl a` 证明 `a = a`，最后 `.mpr` 打回 tuple 层面。
- `symm`：以第一个方向为例：
  - `h : tuple a = tuple b`
  - `(tuple_inj a b).mp h : a = b`
  - `Eq.symm` 反转得到 `b = a`
  - `(tuple_inj b a).mpr` 将 `b = a` 打到 tuple 层面，得到 `tuple b = tuple a`
- `trans`：
  - 先用 `(tuple_inj a b).mp` 将 `hab : tuple a = tuple b` 打到 function 层面，得 `hab' : a = b`
  - 同理 `hbc` 得 `hbc' : b = c`
  - `hab'.trans hbc'` 得 `a = c`
  - `(tuple_inj a c).mpr` 将 `a = c` 打回 tuple 层面，得 `tuple a = tuple c`

## 设计意图

这道题的核心在于理解「表示层面」与「被表示对象层面」的区别：

- 对于 `OrderedPair`，它直接是一个结构体，`OrderedPair.eq` 揭示了结构体相等与其分量相等的等价关系。
- 对于 `tuple`，`tuple a` 是一个 `Object`，而 `a` 是一个函数。它们之间的相等需要 `tuple_inj` 来桥接。

练习的目的是让读者意识到：在处理非平凡的编码（如 Kuratowski 对、tuple）时，等式的传递需要在两个层面之间来回切换。
