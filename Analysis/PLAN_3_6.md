# Plan: Solving `sorry` parts in Section_3_6.lean

## Order (easy→hard, respecting dependencies)

| # | Theorem | Lines | Difficulty | Dependencies | Strategy |
|---|---------|-------|-----------|--------------|----------|
| 1 | `two_to_two_iff` | 1129-1130 | Medium | None | Direct proof: (→) use injectivity + card_image_inj; (←) contrapositive using 2-element set {a,b} with f a = f b |
| 2 | `pow_prod_pow_EqualCard_pow_union` | 1035-1036 | Medium | None | Construct bijection: restrict/piece together functions via B∩C=∅ |
| 3 | `card_pow` | 996-997 | Medium | (2) | Induction on X.card using card_insert + pow_prod_pow_EqualCard_pow_union + card_prod |
| 4 | `pigeonhole_principle` | 1125-1126 | Harder | None | Use card_union_add_card_inter or contradiction via card_subset |
| 5 | `Permutations_ih` (equiv part) | 1523 | Hard | perm_equiv_equiv, succAbove, predAbove | Construct S i ≃ Permutations n via predAbove/succAbove |
| 6 | `Permutations_ih` (rest) | 1527 | Hard | (5) + card_iUnion_card_disjoint | Apply card_iUnion_card_disjoint with pairwise disjoint S i |
| 7 | `Permutations_card` | 1530-1531 | Hard | (6) | Induction on n using Permutations_ih |

## Progress Tracking

- [ ] `two_to_two_iff` — Exercise 3.6.11
- [ ] `pow_prod_pow_EqualCard_pow_union`
- [ ] `card_pow` — Proposition 3.6.14 (f)
- [ ] `pigeonhole_principle` — Exercise 3.6.10
- [ ] `Permutations_ih` inner equiv — Exercise 3.6.12 (i)
- [ ] `Permutations_ih` outer — Exercise 3.6.12 (i)
- [ ] `Permutations_card` — Exercise 3.6.12 (ii)
