---
title     : "Assignment4: TSPL Assignment 4"
permalink : /TSPL/2022/Assignment4/

Name: Yanbo Liu
Email: s2307574@ed.ac.uk
---

```
module Assignment4 where
```

## YOUR NAME AND EMAIL GOES HERE

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises labelled "(practice)" are included for those who want extra practice.

Submit your homework using the "submit" command.
Please ensure your files execute correctly under Agda!


## Good Scholarly Practice.

Please remember the University requirement as
regards all assessed work. Details about this can be found at:

> [https://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct](https://web.inf.ed.ac.uk/infweb/admin/policies/academic-misconduct)

Furthermore, you are required to take reasonable measures to protect
your assessed work from unauthorised access. For example, if you put
any such work on a public repository then you must set access
permissions appropriately (generally permitting access only to
yourself, or your group in the case of group practicals).


## DeBruijn

```
module DeBruijn where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Decidable using (True; toWitness)
```

```
  open import plfa.part2.DeBruijn
    hiding ()
```

#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers, now adapted to the intrinsically-typed
de Bruijn representation.

```agda
  mul : ∀ {Γ} → Γ ⊢ `ℕ ⇒ `ℕ ⇒ `ℕ
  mul = μ ƛ ƛ (case (# 1) (`zero) (plus · # 1 · (# 3 · # 0 · # 1)))
```


#### Exercise `V¬—→` (practice)

Following the previous development, show values do
not reduce, and its corollary, terms that reduce are not
values.

```agda
  -- Your code goes here
```

#### Exercise `mul-example` (recommended)

Using the evaluator, confirm that two times two is four.

```agda
  -- It loaded for a really long time, so I comment it out.
  -- _ : eval (gas 100) (mul · two · two) ≡ steps
  --   ((μ
  --     (ƛ
  --     (ƛ
  --       case (` (S Z)) `zero
  --       ((μ
  --         (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` (S Z)
  --       · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --   · `suc (`suc `zero)
  --   · `suc (`suc `zero)
  --   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
  --   (ƛ
  --     (ƛ
  --     case (` (S Z)) `zero
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` (S Z)
  --       ·
  --       ((μ
  --         (ƛ
  --         (ƛ
  --           case (` (S Z)) `zero
  --           ((μ
  --             (ƛ
  --             (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --           · ` (S Z)
  --           · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z)))))
  --   · `suc (`suc `zero)
  --   · `suc (`suc `zero)
  --   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) `zero
  --     ((μ
  --       (ƛ
  --       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · ` (S Z)
  --     ·
  --     ((μ
  --       (ƛ
  --         (ƛ
  --         case (` (S Z)) `zero
  --         ((μ
  --           (ƛ
  --             (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --           · ` (S Z)
  --           · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   · `suc (`suc `zero)
  --   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
  --   case (`suc (`suc `zero)) `zero
  --   ((μ
  --     (ƛ
  --       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · `suc (`suc `zero)
  --     ·
  --     ((μ
  --       (ƛ
  --       (ƛ
  --         case (` (S Z)) `zero
  --         ((μ
  --           (ƛ
  --           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` (S Z)
  --         · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · ` Z
  --     · `suc (`suc `zero)))
  --   —→⟨ β-suc (V-suc V-zero) ⟩
  --   (μ
  --     (ƛ
  --     (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --   · `suc (`suc `zero)
  --   ·
  --   ((μ
  --     (ƛ
  --       (ƛ
  --       case (` (S Z)) `zero
  --       ((μ
  --         (ƛ
  --           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` (S Z)
  --         · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · `suc `zero
  --     · `suc (`suc `zero))
  --   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
  --   (ƛ
  --     (ƛ
  --     case (` (S Z)) (` Z)
  --     (`suc
  --       ((μ
  --         (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z)))))
  --   · `suc (`suc `zero)
  --   ·
  --   ((μ
  --     (ƛ
  --       (ƛ
  --       case (` (S Z)) `zero
  --       ((μ
  --         (ƛ
  --           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` (S Z)
  --         · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · `suc `zero
  --     · `suc (`suc `zero))
  --   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   ((μ
  --     (ƛ
  --       (ƛ
  --       case (` (S Z)) `zero
  --       ((μ
  --         (ƛ
  --           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` (S Z)
  --         · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · `suc `zero
  --     · `suc (`suc `zero))
  --   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   ((ƛ
  --     (ƛ
  --       case (` (S Z)) `zero
  --       ((μ
  --         (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` (S Z)
  --       ·
  --       ((μ
  --         (ƛ
  --           (ƛ
  --           case (` (S Z)) `zero
  --           ((μ
  --             (ƛ
  --               (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --             · ` (S Z)
  --             · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` Z
  --         · ` (S Z)))))
  --     · `suc `zero
  --     · `suc (`suc `zero))
  --   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   ((ƛ
  --     case (`suc `zero) `zero
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` (S Z)
  --       ·
  --       ((μ
  --         (ƛ
  --         (ƛ
  --           case (` (S Z)) `zero
  --           ((μ
  --             (ƛ
  --             (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --           · ` (S Z)
  --           · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --     · `suc (`suc `zero))
  --   —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   case (`suc `zero) `zero
  --   ((μ
  --     (ƛ
  --       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · `suc (`suc `zero)
  --     ·
  --     ((μ
  --       (ƛ
  --       (ƛ
  --         case (` (S Z)) `zero
  --         ((μ
  --           (ƛ
  --           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` (S Z)
  --         · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · ` Z
  --     · `suc (`suc `zero)))
  --   —→⟨ ξ-·₂ V-ƛ (β-suc V-zero) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   ((μ
  --     (ƛ
  --       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · `suc (`suc `zero)
  --     ·
  --     ((μ
  --       (ƛ
  --       (ƛ
  --         case (` (S Z)) `zero
  --         ((μ
  --           (ƛ
  --           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` (S Z)
  --         · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · `zero
  --     · `suc (`suc `zero)))
  --   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   ((ƛ
  --     (ƛ
  --       case (` (S Z)) (` Z)
  --       (`suc
  --       ((μ
  --         (ƛ
  --           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` Z
  --         · ` (S Z)))))
  --     · `suc (`suc `zero)
  --     ·
  --     ((μ
  --       (ƛ
  --       (ƛ
  --         case (` (S Z)) `zero
  --         ((μ
  --           (ƛ
  --           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` (S Z)
  --         · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · `zero
  --     · `suc (`suc `zero)))
  --   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   ((ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --       ((μ
  --         (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --     ·
  --     ((μ
  --       (ƛ
  --       (ƛ
  --         case (` (S Z)) `zero
  --         ((μ
  --           (ƛ
  --           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` (S Z)
  --         · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · `zero
  --     · `suc (`suc `zero)))
  --   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ))) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   ((ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --       ((μ
  --         (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --     ·
  --     ((ƛ
  --       (ƛ
  --       case (` (S Z)) `zero
  --       ((μ
  --         (ƛ
  --           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` (S Z)
  --         ·
  --         ((μ
  --           (ƛ
  --           (ƛ
  --             case (` (S Z)) `zero
  --             ((μ
  --               (ƛ
  --               (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --             · ` (S Z)
  --             · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` Z
  --         · ` (S Z)))))
  --     · `zero
  --     · `suc (`suc `zero)))
  --   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-zero))) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   ((ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --       ((μ
  --         (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --     ·
  --     ((ƛ
  --       case `zero `zero
  --       ((μ
  --         (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` (S Z)
  --       ·
  --       ((μ
  --         (ƛ
  --           (ƛ
  --           case (` (S Z)) `zero
  --           ((μ
  --             (ƛ
  --               (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --             · ` (S Z)
  --             · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` Z
  --         · ` (S Z))))
  --     · `suc (`suc `zero)))
  --   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   ((ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --       ((μ
  --         (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --     ·
  --     case `zero `zero
  --     ((μ
  --       (ƛ
  --       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · `suc (`suc `zero)
  --     ·
  --     ((μ
  --       (ƛ
  --         (ƛ
  --         case (` (S Z)) `zero
  --         ((μ
  --           (ƛ
  --             (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --           · ` (S Z)
  --           · (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · `suc (`suc `zero))))
  --   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ β-zero) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   ((ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --       ((μ
  --         (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --     · `zero)
  --   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   case (`suc (`suc `zero)) `zero
  --   (`suc
  --     ((μ
  --       (ƛ
  --       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · ` Z
  --     · `zero))
  --   —→⟨ ξ-·₂ V-ƛ (β-suc (V-suc V-zero)) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   `suc
  --   ((μ
  --     (ƛ
  --       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · `suc `zero
  --     · `zero)
  --   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   `suc
  --   ((ƛ
  --     (ƛ
  --       case (` (S Z)) (` Z)
  --       (`suc
  --       ((μ
  --         (ƛ
  --           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` Z
  --         · ` (S Z)))))
  --     · `suc `zero
  --     · `zero)
  --   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero)))) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   `suc
  --   ((ƛ
  --     case (`suc `zero) (` Z)
  --     (`suc
  --       ((μ
  --         (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --     · `zero)
  --   —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-ƛ V-zero)) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   `suc
  --   case (`suc `zero) `zero
  --   (`suc
  --     ((μ
  --       (ƛ
  --       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · ` Z
  --     · `zero))
  --   —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-suc V-zero)) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   `suc
  --   (`suc
  --     ((μ
  --       (ƛ
  --       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · `zero
  --     · `zero))
  --   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ)))) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   `suc
  --   (`suc
  --     ((ƛ
  --       (ƛ
  --       case (` (S Z)) (` Z)
  --       (`suc
  --         ((μ
  --           (ƛ
  --           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` Z
  --         · ` (S Z)))))
  --     · `zero
  --     · `zero))
  --   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero)))) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   `suc
  --   (`suc
  --     ((ƛ
  --       case `zero (` Z)
  --       (`suc
  --       ((μ
  --         (ƛ
  --           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` Z
  --         · ` (S Z))))
  --     · `zero))
  --   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (β-ƛ V-zero))) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   ·
  --   `suc
  --   (`suc
  --     case `zero `zero
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · `zero)))
  --   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc β-zero)) ⟩
  --   (ƛ
  --     case (`suc (`suc `zero)) (` Z)
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --   · `suc (`suc `zero)
  --   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
  --   case (`suc (`suc `zero)) (`suc (`suc `zero))
  --   (`suc
  --     ((μ
  --       (ƛ
  --       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · ` Z
  --     · `suc (`suc `zero)))
  --   —→⟨ β-suc (V-suc V-zero) ⟩
  --   `suc
  --   ((μ
  --     (ƛ
  --       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · `suc `zero
  --     · `suc (`suc `zero))
  --   —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
  --   `suc
  --   ((ƛ
  --     (ƛ
  --       case (` (S Z)) (` Z)
  --       (`suc
  --       ((μ
  --         (ƛ
  --           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` Z
  --         · ` (S Z)))))
  --     · `suc `zero
  --     · `suc (`suc `zero))
  --   —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
  --   `suc
  --   ((ƛ
  --     case (`suc `zero) (` Z)
  --     (`suc
  --       ((μ
  --         (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · ` (S Z))))
  --     · `suc (`suc `zero))
  --   —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
  --   `suc
  --   case (`suc `zero) (`suc (`suc `zero))
  --   (`suc
  --     ((μ
  --       (ƛ
  --       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · ` Z
  --     · `suc (`suc `zero)))
  --   —→⟨ ξ-suc (β-suc V-zero) ⟩
  --   `suc
  --   (`suc
  --     ((μ
  --       (ƛ
  --       (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --     · `zero
  --     · `suc (`suc `zero)))
  --   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
  --   `suc
  --   (`suc
  --     ((ƛ
  --       (ƛ
  --       case (` (S Z)) (` Z)
  --       (`suc
  --         ((μ
  --           (ƛ
  --           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` Z
  --         · ` (S Z)))))
  --     · `zero
  --     · `suc (`suc `zero)))
  --   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
  --   `suc
  --   (`suc
  --     ((ƛ
  --       case `zero (` Z)
  --       (`suc
  --       ((μ
  --         (ƛ
  --           (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --         · ` Z
  --         · ` (S Z))))
  --     · `suc (`suc `zero)))
  --   —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
  --   `suc
  --   (`suc
  --     case `zero (`suc (`suc `zero))
  --     (`suc
  --     ((μ
  --       (ƛ
  --         (ƛ case (` (S Z)) (` Z) (`suc (` (S (S (S Z))) · ` Z · ` (S Z))))))
  --       · ` Z
  --       · `suc (`suc `zero))))
  --   —→⟨ ξ-suc (ξ-suc β-zero) ⟩ `suc (`suc (`suc (`suc `zero))) ∎)
  --   (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
  -- _ = refl
```



## More

```
module More where
```

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Nat using (ℕ; zero; suc; _*_; _<_; _≤?_; z≤n; s≤s)
  open import Relation.Nullary using (¬_)
  open import Relation.Nullary.Decidable using (True; toWitness)
```

```
  -- open import plfa.part2.More
  --   hiding (double-subst)
```

#### Exercise `More` (recommended and practice)

Formalise the remaining constructs defined in this chapter.
Make your changes in this file.
Evaluate each example, applied to data as needed,
to confirm it returns the expected answer:

  * sums (recommended)
  * unit type (practice)
  * an alternative formulation of unit type (practice)
  * empty type (recommended)
  * lists (practice)

```agda
  infix  4 _⊢_
  infix  4 _∋_
  infixl 5 _,_

  infixr 7 _⇒_
  infixr 9 _`×_

  infix  5 ƛ_
  infix  5 μ_
  infixl 7 _·_
  infixl 8 _`*_
  infix  8 `suc_
  infix  9 `_
  infix  9 S_
  infix  9 #_

  data Type : Set where
    `ℕ    : Type
    _⇒_   : Type → Type → Type
    Nat   : Type
    _`×_  : Type → Type → Type
    _`⊎_  : Type → Type → Type
    `⊥    : Type
  
  data Context : Set where
    ∅   : Context
    _,_ : Context → Type → Context

  data _∋_ : Context → Type → Set where

    Z : ∀ {Γ A}
        ---------
      → Γ , A ∋ A

    S_ : ∀ {Γ A B}
      → Γ ∋ B
        ---------
      → Γ , A ∋ B
  
  data _⊢_ : Context → Type → Set where

    -- variables

    `_ : ∀ {Γ A}
      → Γ ∋ A
        -----
      → Γ ⊢ A

    -- functions

    ƛ_  :  ∀ {Γ A B}
      → Γ , A ⊢ B
        ---------
      → Γ ⊢ A ⇒ B

    _·_ : ∀ {Γ A B}
      → Γ ⊢ A ⇒ B
      → Γ ⊢ A
        ---------
      → Γ ⊢ B

    -- naturals

    `zero : ∀ {Γ}
        ------
      → Γ ⊢ `ℕ

    `suc_ : ∀ {Γ}
      → Γ ⊢ `ℕ
        ------
      → Γ ⊢ `ℕ

    case : ∀ {Γ A}
      → Γ ⊢ `ℕ
      → Γ ⊢ A
      → Γ , `ℕ ⊢ A
        -----
      → Γ ⊢ A

    -- fixpoint

    μ_ : ∀ {Γ A}
      → Γ , A ⊢ A
        ----------
      → Γ ⊢ A

    -- primitive numbers

    con : ∀ {Γ}
      → ℕ
        -------
      → Γ ⊢ Nat

    _`*_ : ∀ {Γ}
      → Γ ⊢ Nat
      → Γ ⊢ Nat
        -------
      → Γ ⊢ Nat

    -- let

    `let : ∀ {Γ A B}
      → Γ ⊢ A
      → Γ , A ⊢ B
        ----------
      → Γ ⊢ B
    
    --sums
    `inj₁ : ∀ {Γ A B}
      → Γ ⊢ A
      → Γ ⊢ A `⊎ B
    
    `inj₂ : ∀ {Γ A B}
      → Γ ⊢ B
      → Γ ⊢ A `⊎ B

    case⊎ : ∀ {Γ A B C}
      → Γ ⊢ A `⊎ B
      → Γ , A ⊢ C
      → Γ , B ⊢ C
      → Γ ⊢ C

    -- product
    `⟨_,_⟩ : ∀ {Γ A B}
      → Γ ⊢ A
      → Γ ⊢ B
        -----------
      → Γ ⊢ A `× B

    `proj₁ : ∀ {Γ A B}
      → Γ ⊢ A `× B
        -----------
      → Γ ⊢ A

    `proj₂ : ∀ {Γ A B}
      → Γ ⊢ A `× B
        -----------
      → Γ ⊢ B
     
    -- alternative formulation of products

    case× : ∀ {Γ A B C}
      → Γ ⊢ A `× B
      → Γ , A , B ⊢ C
        --------------
      → Γ ⊢ C
    --empty
    case⊥ :  ∀ {Γ A}
      → Γ ⊢ `⊥
      → Γ ⊢ A

  length : Context → ℕ
  length ∅        =  zero
  length (Γ , _)  =  suc (length Γ)

  lookup : {Γ : Context} → {n : ℕ} → (p : n < length Γ) → Type
  lookup {(_ , A)} {zero}    (s≤s z≤n)  =  A
  lookup {(Γ , _)} {(suc n)} (s≤s p)    =  lookup p

  count : ∀ {Γ} → {n : ℕ} → (p : n < length Γ) → Γ ∋ lookup p
  count {_ , _} {zero}    (s≤s z≤n)  =  Z
  count {Γ , _} {(suc n)} (s≤s p)    =  S (count p)

  #_ : ∀ {Γ}
    → (n : ℕ)
    → {n∈Γ : True (suc n ≤? length Γ)}
      --------------------------------
    → Γ ⊢ lookup (toWitness n∈Γ)
  #_ n {n∈Γ}  =  ` count (toWitness n∈Γ)
  ext : ∀ {Γ Δ}
    → (∀ {A}   →     Γ ∋ A →     Δ ∋ A)
      ---------------------------------
    → (∀ {A B} → Γ , A ∋ B → Δ , A ∋ B)
  ext ρ Z      =  Z
  ext ρ (S x)  =  S (ρ x)

  rename : ∀ {Γ Δ}
    → (∀ {A} → Γ ∋ A → Δ ∋ A)
      -----------------------
    → (∀ {A} → Γ ⊢ A → Δ ⊢ A)
  rename ρ (` x)          =  ` (ρ x)
  rename ρ (ƛ N)          =  ƛ (rename (ext ρ) N)
  rename ρ (L · M)        =  (rename ρ L) · (rename ρ M)
  rename ρ (`zero)        =  `zero
  rename ρ (`suc M)       =  `suc (rename ρ M)
  rename ρ (case L M N)   =  case (rename ρ L) (rename ρ M) (rename (ext ρ) N)
  rename ρ (μ N)          =  μ (rename (ext ρ) N)
  rename ρ (con n)        =  con n
  rename ρ (M `* N)       =  rename ρ M `* rename ρ N
  rename ρ (`let M N)     =  `let (rename ρ M) (rename (ext ρ) N)
  rename ρ `⟨ M , N ⟩     =  `⟨ rename ρ M , rename ρ N ⟩
  rename ρ (`proj₁ L)     =  `proj₁ (rename ρ L)
  rename ρ (`proj₂ L)     =  `proj₂ (rename ρ L)
  rename ρ (case× L M)    =  case× (rename ρ L) (rename (ext (ext ρ)) M)
  rename ρ (`inj₁ L)     = `inj₁ (rename ρ L)
  rename ρ (`inj₂ L)     = `inj₂ (rename ρ L)
  rename ρ (case⊎ L1 L2 L3) = case⊎ (rename ρ L1 ) (rename (ext ρ) L2) (rename (ext ρ) L3)
  rename ρ (case⊥ bot)   = case⊥ (rename ρ bot )

  exts : ∀ {Γ Δ} → (∀ {A} → Γ ∋ A → Δ ⊢ A) → (∀ {A B} → Γ , A ∋ B → Δ , A ⊢ B)
  exts σ Z      =  ` Z
  exts σ (S x)  =  rename S_ (σ x)

  subst : ∀ {Γ Δ} → (∀ {C} → Γ ∋ C → Δ ⊢ C) → (∀ {C} → Γ ⊢ C → Δ ⊢ C)
  subst σ (` k)          =  σ k
  subst σ (ƛ N)          =  ƛ (subst (exts σ) N)
  subst σ (L · M)        =  (subst σ L) · (subst σ M)
  subst σ (`zero)        =  `zero
  subst σ (`suc M)       =  `suc (subst σ M)
  subst σ (case L M N)   =  case (subst σ L) (subst σ M) (subst (exts σ) N)
  subst σ (μ N)          =  μ (subst (exts σ) N)
  subst σ (con n)        =  con n
  subst σ (M `* N)       =  subst σ M `* subst σ N
  subst σ (`let M N)     =  `let (subst σ M) (subst (exts σ) N)
  subst σ `⟨ M , N ⟩      =  `⟨ subst σ M , subst σ N ⟩
  subst σ (`proj₁ L)     =  `proj₁ (subst σ L)
  subst σ (`proj₂ L)     =  `proj₂ (subst σ L)
  subst σ (case× L M)    =  case× (subst σ L) (subst (exts (exts σ)) M)
  subst σ (`inj₁ L)      = `inj₁ (subst σ L)
  subst σ (`inj₂ L)      = `inj₂ (subst σ L)
  subst σ (case⊎ L1 L2 L3) = case⊎ (subst σ L1 ) (subst (exts σ) L2) (subst (exts σ) L3)
  subst σ  (case⊥ bot)   = case⊥ (subst σ bot )
  substZero : ∀ {Γ}{A B} → Γ ⊢ A → Γ , A ∋ B → Γ ⊢ B
  substZero V Z      =  V
  substZero V (S x)  =  ` x

  _[_] : ∀ {Γ A B}
    → Γ , A ⊢ B
    → Γ ⊢ A
      ---------
    → Γ ⊢ B
  _[_] {Γ} {A} N V =  subst {Γ , A} {Γ} (substZero V) N

  _[_][_] : ∀ {Γ A B C}
    → Γ , A , B ⊢ C
    → Γ ⊢ A
    → Γ ⊢ B
      -------------
    → Γ ⊢ C
  _[_][_] {Γ} {A} {B} N V W =  subst {Γ , A , B} {Γ} σ N
    where
    σ : ∀ {C} → Γ , A , B ∋ C → Γ ⊢ C
    σ Z          =  W
    σ (S Z)      =  V
    σ (S (S x))  =  ` x
  
  data Value : ∀ {Γ A} → Γ ⊢ A → Set where

  -- functions

    V-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B}
        ---------------------------
      → Value (ƛ N)

    -- naturals

    V-zero : ∀ {Γ}
        -----------------
      → Value (`zero {Γ})

    V-suc_ : ∀ {Γ} {V : Γ ⊢ `ℕ}
      → Value V
        --------------
      → Value (`suc V)

    -- primitives

    V-con : ∀ {Γ n}
        -----------------
      → Value (con {Γ} n)

    -- products

    V-⟨_,_⟩ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V
      → Value W 
        ----------------
      → Value `⟨ V , W ⟩
    
    -- sums
    V-inj₁ : ∀ {Γ A B} {V : Γ ⊢ A}
      → Value (V)
      → Value  (`inj₁ {Γ} {A} {B} V)

    V-inj₂ : ∀ {Γ A B} {W : Γ ⊢ B}
      → Value (W)
      → Value (`inj₂ {Γ} {A} {B} W)
  infix 2 _—→_

  data _—→_ : ∀ {Γ A} → (Γ ⊢ A) → (Γ ⊢ A) → Set where

    -- functions

    ξ-·₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A ⇒ B} {M : Γ ⊢ A}
      → L —→ L′
        ---------------
      → L · M —→ L′ · M

    ξ-·₂ : ∀ {Γ A B} {V : Γ ⊢ A ⇒ B} {M M′ : Γ ⊢ A}
      → Value V
      → M —→ M′
        ---------------
      → V · M —→ V · M′

    β-ƛ : ∀ {Γ A B} {N : Γ , A ⊢ B} {V : Γ ⊢ A}
      → Value V
        --------------------
      → (ƛ N) · V —→ N [ V ]

    -- naturals

    ξ-suc : ∀ {Γ} {M M′ : Γ ⊢ `ℕ}
      → M —→ M′
        -----------------
      → `suc M —→ `suc M′

    ξ-case : ∀ {Γ A} {L L′ : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      → L —→ L′
        -------------------------
      → case L M N —→ case L′ M N

    β-zero :  ∀ {Γ A} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
        -------------------
      → case `zero M N —→ M

    β-suc : ∀ {Γ A} {V : Γ ⊢ `ℕ} {M : Γ ⊢ A} {N : Γ , `ℕ ⊢ A}
      → Value V
        ----------------------------
      → case (`suc V) M N —→ N [ V ]

    -- fixpoint

    β-μ : ∀ {Γ A} {N : Γ , A ⊢ A}
        ----------------
      → μ N —→ N [ μ N ]

    -- primitive numbers

    ξ-*₁ : ∀ {Γ} {L L′ M : Γ ⊢ Nat}
      → L —→ L′
        -----------------
      → L `* M —→ L′ `* M

    ξ-*₂ : ∀ {Γ} {V M M′ : Γ ⊢ Nat}
      → Value V
      → M —→ M′
        -----------------
      → V `* M —→ V `* M′

    δ-* : ∀ {Γ c d}
        ---------------------------------
      → con {Γ} c `* con d —→ con (c * d)

    -- let

    ξ-let : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ , A ⊢ B}
      → M —→ M′
        ---------------------
      → `let M N —→ `let M′ N

    β-let : ∀ {Γ A B} {V : Γ ⊢ A} {N : Γ , A ⊢ B}
      → Value V
        -------------------
      → `let V N —→ N [ V ]
    --sums 

    ξ-inj₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A}
      → M —→ M′
      → `inj₁ {Γ} {A} {B} M —→ `inj₁ M′
    
    ξ-inj₂ : ∀ {Γ A B} {N N′ : Γ ⊢ B} 
      → N —→ N′
      → `inj₂ {Γ} {A} {B} N —→ `inj₂ N′
    
    ξ-case⊎ : ∀ {Γ A B C} {L L′ : Γ ⊢ A `⊎ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C }
      → L —→ L′
      → case⊎ L M N —→ case⊎ L′ M N

    
    β-inj₁ : ∀ {Γ A B C} {V : Γ ⊢ A} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C }
      → Value V
      → case⊎ (`inj₁ V) M N   —→ M [ V ]

    β-inj₂ : ∀ {Γ A B C} {W : Γ ⊢ B} {M : Γ , A ⊢ C} {N : Γ , B ⊢ C }
      → Value W
      → case⊎ (`inj₂ W) M N   —→  N [ W ]
    -- products

    ξ-⟨,⟩₁ : ∀ {Γ A B} {M M′ : Γ ⊢ A} {N : Γ ⊢ B}
      → M —→ M′
        -------------------------
      → `⟨ M , N ⟩ —→ `⟨ M′ , N ⟩

    ξ-⟨,⟩₂ : ∀ {Γ A B} {V : Γ ⊢ A} {N N′ : Γ ⊢ B}
      → Value V
      → N —→ N′
        -------------------------
      → `⟨ V , N ⟩ —→ `⟨ V , N′ ⟩

    ξ-proj₁ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
      → L —→ L′
        ---------------------
      → `proj₁ L —→ `proj₁ L′

    ξ-proj₂ : ∀ {Γ A B} {L L′ : Γ ⊢ A `× B}
      → L —→ L′
        ---------------------
      → `proj₂ L —→ `proj₂ L′

    β-proj₁ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V
      → Value W
        ----------------------
      → `proj₁ `⟨ V , W ⟩ —→ V

    β-proj₂ : ∀ {Γ A B} {V : Γ ⊢ A} {W : Γ ⊢ B}
      → Value V
      → Value W
        ----------------------
      → `proj₂ `⟨ V , W ⟩ —→ W

    -- alternative formulation of products

    ξ-case× : ∀ {Γ A B C} {L L′ : Γ ⊢ A `× B} {M : Γ , A , B ⊢ C}
      → L —→ L′
        -----------------------
      → case× L M —→ case× L′ M

    β-case× : ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {M : Γ , A , B ⊢ C}
      → Value V
      → Value W
        ----------------------------------
      → case× `⟨ V , W ⟩ M —→ M [ V ][ W ]
    
    -- Empty
    ξ-case⊥ : ∀ {Γ A} {L L′ : Γ ⊢ `⊥ }
      → L —→ L′
      → case⊥ {Γ} {A}  L —→ case⊥ L′

  infix  2 _—↠_
  infix  1 begin_
  infixr 2 _—→⟨_⟩_
  infix  3 _∎

  data _—↠_ {Γ A} : (Γ ⊢ A) → (Γ ⊢ A) → Set where

    _∎ : (M : Γ ⊢ A)
        ------
      → M —↠ M

    _—→⟨_⟩_ : (L : Γ ⊢ A) {M N : Γ ⊢ A}
      → L —→ M
      → M —↠ N
        ------
      → L —↠ N
  begin_ : ∀ {Γ A} {M N : Γ ⊢ A}
    → M —↠ N
      ------
    → M —↠ N
  begin M—↠N = M—↠N

  V¬—→ : ∀ {Γ A} {M N : Γ ⊢ A}
    → Value M
      ----------
    → ¬ (M —→ N)
  V¬—→ V-ƛ          ()
  V¬—→ V-zero       ()
  V¬—→ (V-suc VM)   (ξ-suc M—→M′)     =  V¬—→ VM M—→M′
  V¬—→ V-con        ()
  V¬—→ V-⟨ VM , _ ⟩ (ξ-⟨,⟩₁ M—→M′)    =  V¬—→ VM M—→M′
  V¬—→ V-⟨ _ , VN ⟩ (ξ-⟨,⟩₂ _ N—→N′)  =  V¬—→ VN N—→N′
  V¬—→ {A = A `⊎ B} (V-inj₁ VM) ( ξ-inj₁ M—→N) = V¬—→ VM M—→N
  V¬—→ {A = A `⊎ B} (V-inj₂ VN) ( ξ-inj₂ M—→N) = V¬—→ VN M—→N
  
  data Progress {A} (M : ∅ ⊢ A) : Set where
    step : ∀ {N : ∅ ⊢ A}
      → M —→ N
        ----------
      → Progress M

    done :
        Value M
        ----------
      → Progress M
  
  progress : ∀ {A}
    → (M : ∅ ⊢ A)
      -----------
    → Progress M
  progress (` ())
  progress (ƛ N)                              =  done V-ƛ
  progress (L · M) with progress L
  ...    | step L—→L′                         =  step (ξ-·₁ L—→L′)
  ...    | done V-ƛ with progress M
  ...        | step M—→M′                     =  step (ξ-·₂ V-ƛ M—→M′)
  ...        | done VM                        =  step (β-ƛ VM)
  progress (`zero)                            =  done V-zero
  progress (`suc M) with progress M
  ...    | step M—→M′                         =  step (ξ-suc M—→M′)
  ...    | done VM                            =  done (V-suc VM)
  progress (case L M N) with progress L
  ...    | step L—→L′                         =  step (ξ-case L—→L′)
  ...    | done V-zero                        =  step β-zero
  ...    | done (V-suc VL)                    =  step (β-suc VL)
  progress (μ N)                              =  step β-μ
  progress (con n)                            =  done V-con
  progress (L `* M) with progress L
  ...    | step L—→L′                         =  step (ξ-*₁ L—→L′)
  ...    | done V-con with progress M
  ...        | step M—→M′                     =  step (ξ-*₂ V-con M—→M′)
  ...        | done V-con                     =  step δ-*
  progress (`let M N) with progress M
  ...    | step M—→M′                         =  step (ξ-let M—→M′)
  ...    | done VM                            =  step (β-let VM)
  progress `⟨ M , N ⟩ with progress M
  ...    | step M—→M′                         =  step (ξ-⟨,⟩₁ M—→M′)
  ...    | done VM with progress N
  ...        | step N—→N′                     =  step (ξ-⟨,⟩₂ VM N—→N′)
  ...        | done VN                        =  done (V-⟨ VM , VN ⟩)
  progress (`proj₁ L) with progress L
  ...    | step L—→L′                         =  step (ξ-proj₁ L—→L′)
  ...    | done (V-⟨ VM , VN ⟩)               =  step (β-proj₁ VM VN)
  progress (`proj₂ L) with progress L
  ...    | step L—→L′                         =  step (ξ-proj₂ L—→L′)
  ...    | done (V-⟨ VM , VN ⟩)               =  step (β-proj₂ VM VN)
  progress (case× L M) with progress L
  ...    | step L—→L′                         =  step (ξ-case× L—→L′)
  ...    | done (V-⟨ VM , VN ⟩)               =  step (β-case× VM VN)
  progress (`inj₁ M) with progress M 
  ...    | step M—→M′                         =  step (ξ-inj₁ M—→M′ )
  ...    | done VM                   =  done ( V-inj₁ VM )
  progress (`inj₂ M) with progress M 
  ...    | step M—→M′                         =  step (ξ-inj₂ M—→M′ )
  ...    | done VM                   =  done ( V-inj₂ VM )
  progress (case⊎ L1 L2 L3) with progress L1 
  ...    | step M—→M′                         =  step (ξ-case⊎ M—→M′ )
  ...    | done (V-inj₁ VM)                   =  step (β-inj₁ VM)
  ...    | done (V-inj₂ VM)                   =  step (β-inj₂ VM)
  progress (case⊥ M) with progress M
  ...    | step M—→M′                         = step (ξ-case⊥ M—→M′ )

  record Gas : Set where
    constructor gas
    field
      amount : ℕ

  data Finished {Γ A} (N : Γ ⊢ A) : Set where

    done :
        Value N
        ----------
      → Finished N

    out-of-gas :
        ----------
        Finished N

  data Steps {A} : ∅ ⊢ A → Set where

    steps : {L N : ∅ ⊢ A}
      → L —↠ N
      → Finished N
        ----------
      → Steps L
  eval : ∀ {A}
    → Gas
    → (L : ∅ ⊢ A)
      -----------
    → Steps L
  eval (gas zero)    L                     =  steps (L ∎) out-of-gas
  eval (gas (suc m)) L with progress L
  ... | done VL                            =  steps (L ∎) (done VL)
  ... | step {M} L—→M with eval (gas m) M
  ...    | steps M—↠N fin                  =  steps (L —→⟨ L—→M ⟩ M—↠N) fin
 
```

```agda
-- example
-- sums
  swap⊎ : ∀ {A B} → ∅ ⊢ A `⊎ B ⇒ B `⊎ A
  swap⊎ = ƛ case⊎ (# 0) (`inj₂ (# 0)) (`inj₁ (# 0))
  
  _ : swap⊎ · (`inj₁ { B = Type.`ℕ }  (con 5)) —↠ (`inj₂ { A = Type.`ℕ } (con 5))
  _ =
    begin 
      (ƛ case⊎ (` Z) (`inj₂ (` Z)) (`inj₁ (` Z))) · `inj₁ (con 5)
    —→⟨ β-ƛ (V-inj₁ V-con) ⟩
      case⊎ (`inj₁ (con 5)) (`inj₂ (` Z)) (`inj₁ (` Z))
    —→⟨ β-inj₁ V-con ⟩
      `inj₂ (con 5)
    ∎
  
  to⊎⊥ : ∀ {A} → ∅ ⊢ A ⇒ A `⊎ `⊥
  to⊎⊥ = ƛ `inj₁ (# 0)

  _ : to⊎⊥ · (con 42) —↠ `inj₁ (con 42 )
  _ =
    begin
      (ƛ `inj₁ (` Z)) · con 42
   —→⟨ β-ƛ V-con ⟩
      `inj₁ (con 42)
    ∎
  
  from⊎⊥ : ∀ {A} → ∅ ⊢ A `⊎ `⊥ ⇒ A
  from⊎⊥ = ƛ case⊎ ( # 0) (# 0) ( case⊥ (# 0) )

  _ : from⊎⊥ · (`inj₁ (con 42)) —↠ (con 42)
  _ =
    begin
      (ƛ case⊎ (` Z) (` Z) (case⊥ (` Z))) · `inj₁ (con 42)
    —→⟨ β-ƛ (V-inj₁ V-con) ⟩
      case⊎ (`inj₁ (con 42)) (` Z) (case⊥ (` Z))
    —→⟨ β-inj₁ V-con ⟩
      con 42
    ∎
```
Please delimit any code you add as follows:

    -- begin
    -- end


#### Exercise `double-subst` (stretch)

Show that a double substitution is equivalent to two single
substitutions.
```agda
  -- postulate
  --   double-subst :
  --     ∀ {Γ A B C} {V : Γ ⊢ A} {W : Γ ⊢ B} {N : Γ , A , B ⊢ C} →
  --       N [ V ][ W ] ≡ (N [ rename S_ W ]) [ V ]
```
Note the arguments need to be swapped and `W` needs to have
its context adjusted via renaming in order for the right-hand
side to be well typed.


## Inference

```
module Inference where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; sym; trans; cong; cong₂; _≢_)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
  open import Data.String using (String; _≟_)
  open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Decidable using (False; toWitnessFalse)
```

Once we have a type derivation, it will be easy to construct
from it the intrinsically-typed representation.  In order that we
can compare with our previous development, we import
module `plfa.part2.More`:

```agda
  import plfa.part2.More as DB

```

The phrase `as DB` allows us to refer to definitions
from that module as, for instance, `DB._⊢_`, which is
invoked as `Γ DB.⊢ A`, where `Γ` has type
`DB.Context` and `A` has type `DB.Type`.


```
  infix   4  _∋_⦂_
  infix   4  _⊢_↑_
  infix   4  _⊢_↓_
  infixl  5  _,_⦂_

  infixr  7  _⇒_

  infix   5  ƛ_⇒_
  infix   5  μ_⇒_
  infix   6  _↑
  infix   6  _↓_
  infixl  7  _·_
  infix   8  `suc_
  infix   9  `_


  Id : Set
  Id = String

  data Type : Set where
    `ℕ    : Type
    _⇒_   : Type → Type → Type
    _`×_   : Type → Type → Type


  data Context : Set where
    ∅     : Context
    _,_⦂_ : Context → Id → Type → Context


  data Term⁺ : Set
  data Term⁻ : Set

  data Term⁺ where
    `_                       : Id → Term⁺
    _·_                      : Term⁺ → Term⁻ → Term⁺
    _↓_                      : Term⁻ → Type → Term⁺
    `proj₁_                  : Term⁺  → Term⁺
    `proj₂_                  : Term⁺  → Term⁺

  data Term⁻ where
    ƛ_⇒_                     : Id → Term⁻ → Term⁻
    `zero                    : Term⁻
    `suc_                    : Term⁻ → Term⁻
    `case_[zero⇒_|suc_⇒_]    : Term⁺ → Term⁻ → Id → Term⁻ → Term⁻
    μ_⇒_                     : Id → Term⁻ → Term⁻
    _↑                       : Term⁺ → Term⁻
    `⟨_,_⟩                    : Term⁻ → Term⁻ → Term⁻

  two : Term⁻
  two = `suc (`suc `zero)

  plus : Term⁺
  plus = (μ "p" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
            `case (` "m") [zero⇒ ` "n" ↑
                          |suc "m" ⇒ `suc (` "p" · (` "m" ↑) · (` "n" ↑) ↑) ])
              ↓ (`ℕ ⇒ `ℕ ⇒ `ℕ)

  2+2 : Term⁺
  2+2 = plus · two · two

  Ch : Type
  Ch = (`ℕ ⇒ `ℕ) ⇒ `ℕ ⇒ `ℕ

  twoᶜ : Term⁻
  twoᶜ = (ƛ "s" ⇒ ƛ "z" ⇒ ` "s" · (` "s" · (` "z" ↑) ↑) ↑)

  plusᶜ : Term⁺
  plusᶜ = (ƛ "m" ⇒ ƛ "n" ⇒ ƛ "s" ⇒ ƛ "z" ⇒
            ` "m" · (` "s" ↑) · (` "n" · (` "s" ↑) · (` "z" ↑) ↑) ↑)
              ↓ (Ch ⇒ Ch ⇒ Ch)

  sucᶜ : Term⁻
  sucᶜ = ƛ "x" ⇒ `suc (` "x" ↑)

  2+2ᶜ : Term⁺
  2+2ᶜ = plusᶜ · twoᶜ · twoᶜ · sucᶜ · `zero

  data _∋_⦂_ : Context → Id → Type → Set where

    Z : ∀ {Γ x A}
        -----------------
      → Γ , x ⦂ A ∋ x ⦂ A

    S : ∀ {Γ x y A B}
      → x ≢ y
      → Γ ∋ x ⦂ A
        -----------------
      → Γ , y ⦂ B ∋ x ⦂ A
```

#### Exercise `bidirectional-mul` (recommended) {#bidirectional-mul}

Rewrite your definition of multiplication from
Chapter [Lambda](/Lambda/), decorated to support inference.

```agda
  mul : Term⁺
  mul = (μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
          `case (` "m") [zero⇒ `zero 
                        |suc "m" ⇒ plus · (` "n" ↑) · (` "*" · (` "m" ↑ ) · (` "n" ↑)↑) ↑ ])
            ↓ (`ℕ ⇒ `ℕ ⇒ `ℕ)
```


#### Exercise `bidirectional-products` (recommended) {#bidirectional-products}

Extend the bidirectional type rules to include products from
Chapter [More](/More/).

```agda
  data _⊢_↑_ : Context → Term⁺ → Type → Set
  data _⊢_↓_ : Context → Term⁻ → Type → Set
  
  data _⊢_↑_ where

    ⊢` : ∀ {Γ A x}
      → Γ ∋ x ⦂ A
        -----------
      → Γ ⊢ ` x ↑ A

    _·_ : ∀ {Γ L M A B}
      → Γ ⊢ L ↑ A ⇒ B
      → Γ ⊢ M ↓ A
        -------------
      → Γ ⊢ L · M ↑ B

    ⊢↓ : ∀ {Γ M A}
      → Γ ⊢ M ↓ A
        ---------------
      → Γ ⊢ (M ↓ A) ↑ A

    ⊢proj₁ : ∀ {Γ M A B}
      → Γ ⊢ M ↑ (A `× B )
      → Γ ⊢ `proj₁ M  ↑ A 
    
    ⊢proj₂ : ∀ {Γ N A B}
      → Γ ⊢ N ↑ (A `× B )
      → Γ ⊢ `proj₂ N  ↑ B 
    
  data _⊢_↓_ where

    ⊢ƛ : ∀ {Γ x N A B}
      → Γ , x ⦂ A ⊢ N ↓ B
        -------------------
      → Γ ⊢ ƛ x ⇒ N ↓ A ⇒ B

    ⊢zero : ∀ {Γ}
        --------------
      → Γ ⊢ `zero ↓ `ℕ

    ⊢suc : ∀ {Γ M}
      → Γ ⊢ M ↓ `ℕ
        ---------------
      → Γ ⊢ `suc M ↓ `ℕ

    ⊢case : ∀ {Γ L M x N A}
      → Γ ⊢ L ↑ `ℕ
      → Γ ⊢ M ↓ A
      → Γ , x ⦂ `ℕ ⊢ N ↓ A
        -------------------------------------
      → Γ ⊢ `case L [zero⇒ M |suc x ⇒ N ] ↓ A

    ⊢μ : ∀ {Γ x N A}
      → Γ , x ⦂ A ⊢ N ↓ A
        -----------------
      → Γ ⊢ μ x ⇒ N ↓ A
    
    `⟨_,_⟩ : ∀ {Γ M N A B}
      → Γ ⊢ M ↓ A 
      → Γ ⊢ N ↓ B
      → Γ ⊢ (`⟨ M , N ⟩) ↓ (A `× B )

    ⊢↑ : ∀ {Γ M A B}
      → Γ ⊢ M ↑ A
      → A ≡ B
        -------------
      → Γ ⊢ (M ↑) ↓ B

       
 
```


#### Exercise `bidirectional-rest` (stretch)

Extend the bidirectional type rules to include the rest of the constructs from
Chapter [More](/More/).

```agda
  -- Your code goes here
```

```agda
  _≟Tp_ : (A B : Type) → Dec (A ≡ B)
  (A `× B) ≟Tp `ℕ            = no λ()
  (A `× B) ≟Tp (A₁ ⇒ B₁)       = no λ()
  (A `× B) ≟Tp (A₁ `× B₁) 
    with A ≟Tp A₁ | B ≟Tp B₁
  ... | yes refl  | yes refl = yes refl
  ... | no A≢     | _        = no λ{refl → A≢ refl}
  ... | _         | no B≢    = no λ{refl → B≢ refl}
  `ℕ ≟Tp (B `× A)            = no λ()
  `ℕ      ≟Tp `ℕ              =  yes refl
  `ℕ      ≟Tp (A ⇒ B)         =  no λ()
  (A ⇒ B) ≟Tp (A₁ `× B₁)      = no λ()
  (A ⇒ B) ≟Tp `ℕ              =  no λ()
  (A ⇒ B) ≟Tp (A′ ⇒ B′)
    with A ≟Tp A′ | B ≟Tp B′
  ...  | no A≢    | _         =  no λ{refl → A≢ refl}
  ...  | yes _    | no B≢     =  no λ{refl → B≢ refl}
  ...  | yes refl | yes refl  =  yes refl
  
  dom≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → A ≡ A′
  dom≡ refl = refl

  rng≡ : ∀ {A A′ B B′} → A ⇒ B ≡ A′ ⇒ B′ → B ≡ B′
  rng≡ refl = refl

  proj₁≡ : ∀ {A A′ B B′} → A `× B ≡ A′ `× B′ → A ≡ A′
  proj₁≡ refl = refl

  proj₂≡ : ∀ {A A′ B B′} → A `× B ≡ A′ `× B′ → B ≡ B′
  proj₂≡ refl = refl
  ℕ≢⇒ : ∀ {A B} → `ℕ ≢ A ⇒ B
  ℕ≢⇒ ()

  ℕ≢x : ∀ {A B} → `ℕ ≢  (A `× B)
  ℕ≢x ()

  x≢⇒ : ∀ {A B C D} → (A ⇒ B) ≢  (C `× D)
  x≢⇒ ()
  
  uniq-∋ : ∀ {Γ x A B} → Γ ∋ x ⦂ A → Γ ∋ x ⦂ B → A ≡ B
  uniq-∋ Z Z                 =  refl
  uniq-∋ Z (S x≢y _)         =  ⊥-elim (x≢y refl)
  uniq-∋ (S x≢y _) Z         =  ⊥-elim (x≢y refl)
  uniq-∋ (S _ ∋x) (S _ ∋x′)  =  uniq-∋ ∋x ∋x′

  uniq-↑ : ∀ {Γ M A B} → Γ ⊢ M ↑ A → Γ ⊢ M ↑ B → A ≡ B
  uniq-↑ (⊢` ∋x) (⊢` ∋x′)       =  uniq-∋ ∋x ∋x′
  uniq-↑ (⊢L · ⊢M) (⊢L′ · ⊢M′)  =  rng≡ (uniq-↑ ⊢L ⊢L′)
  uniq-↑ (⊢↓ ⊢M) (⊢↓ ⊢M′)       =  refl

  uniq-↑ (⊢proj₁ ⊢M) (⊢proj₁ ⊢M′)  = proj₁≡ (uniq-↑ ⊢M ⊢M′ )
  uniq-↑ (⊢proj₂ ⊢N) (⊢proj₂ ⊢N′)  = proj₂≡(uniq-↑ ⊢N ⊢N′ )


  ext∋ : ∀ {Γ B x y}
    → x ≢ y
    → ¬ (∃[ A ] Γ ∋ x ⦂ A)
      ----------------------------
    → ¬ (∃[ A ] Γ , y ⦂ B ∋ x ⦂ A)
  ext∋ x≢y _  ⟨ A , Z ⟩       =  x≢y refl
  ext∋ _   ¬∃ ⟨ A , S _ ∋x ⟩  =  ¬∃ ⟨ A , ∋x ⟩

  lookup : ∀ (Γ : Context) (x : Id)
          ------------------------
        → Dec (∃[ A ] Γ ∋ x ⦂ A)
  lookup ∅ x                        =  no  (λ ())
  lookup (Γ , y ⦂ B) x with x ≟ y
  ... | yes refl                    =  yes ⟨ B , Z ⟩
  ... | no x≢y with lookup Γ x
  ...             | no  ¬∃          =  no  (ext∋ x≢y ¬∃)
  ...             | yes ⟨ A , ∋x ⟩  =  yes ⟨ A , S x≢y ∋x ⟩
  ¬arg : ∀ {Γ A B L M}
    → Γ ⊢ L ↑ A ⇒ B
    → ¬ Γ ⊢ M ↓ A
      --------------------------
    → ¬ (∃[ B′ ] Γ ⊢ L · M ↑ B′)
  ¬arg ⊢L ¬⊢M ⟨ B′ , ⊢L′ · ⊢M′ ⟩ rewrite dom≡ (uniq-↑ ⊢L ⊢L′) = ¬⊢M ⊢M′


  ¬switch : ∀ {Γ M A B}
    → Γ ⊢ M ↑ A
    → A ≢ B
      ---------------
    → ¬ Γ ⊢ (M ↑) ↓ B
  ¬switch ⊢M A≢B (⊢↑ ⊢M′ A′≡B) rewrite uniq-↑ ⊢M ⊢M′ = A≢B A′≡B

  synthesize : ∀ (Γ : Context) (M : Term⁺)
        ---------------------------
      → Dec (∃[ A ] Γ ⊢ M ↑ A )

  inherit : ∀ (Γ : Context) (M : Term⁻) (A : Type)
        ---------------
      → Dec (Γ ⊢ M ↓ A)

  synthesize Γ (` x) with lookup Γ x
  ... | no  ¬∃              =  no  (λ{ ⟨ A , ⊢` ∋x ⟩ → ¬∃ ⟨ A , ∋x ⟩ })
  ... | yes ⟨ A , ∋x ⟩      =  yes ⟨ A , ⊢` ∋x ⟩
  synthesize Γ (L · M) with synthesize Γ L
  ... | no  ¬∃              =  no  (λ{ ⟨ _ , ⊢L  · _  ⟩  →  ¬∃ ⟨ _ , ⊢L ⟩ })
  ... | yes ⟨ `ℕ ,    ⊢L ⟩  =  no  (λ{ ⟨ _ , ⊢L′ · _  ⟩  →  ℕ≢⇒ (uniq-↑ ⊢L ⊢L′) })
  ... | yes ⟨ A `× B , ⊢L ⟩ =  no (λ{ ⟨ _ , ⊢L′ · _  ⟩  →  x≢⇒ (uniq-↑ ⊢L′ ⊢L )}) 
  ... | yes ⟨ A ⇒ B , ⊢L ⟩ with inherit Γ M A
  ...    | no  ¬⊢M          =  no  (¬arg ⊢L ¬⊢M)
  ...    | yes ⊢M           =  yes ⟨ B , ⊢L · ⊢M ⟩
  synthesize Γ (M ↓ A) with inherit Γ M A
  ... | no  ¬⊢M             =  no  (λ{ ⟨ _ , ⊢↓ ⊢M ⟩  →  ¬⊢M ⊢M })
  ... | yes ⊢M              =  yes ⟨ A , ⊢↓ ⊢M ⟩
  synthesize Γ (`proj₁ M) with synthesize Γ M
  ... | no  ¬∃              =  no (λ { ⟨ _ , ⊢proj₁ ⊢M   ⟩ → ¬∃ ⟨ _ , ⊢M ⟩ } )
  ... | yes  ⟨ `ℕ , ⊢M ⟩    =  no (λ { ⟨ _ , ⊢proj₁ ⊢M′ ⟩ → ℕ≢x (uniq-↑ ⊢M ⊢M′)}  )
  ... | yes ⟨ A ⇒ B , ⊢M ⟩  =  no (λ { ⟨ _ , ⊢proj₁ ⊢M′ ⟩ → x≢⇒ (uniq-↑ ⊢M ⊢M′)}  )
  ... | yes ⟨ A `× B , ⊢M ⟩  =  yes ⟨ A , ⊢proj₁ ⊢M ⟩

  synthesize Γ (`proj₂ N) with synthesize Γ N
  ... | no  ¬∃              =  no (λ { ⟨ _ , ⊢proj₂ ⊢N   ⟩ → ¬∃ ⟨ _ , ⊢N ⟩ } )
  ... | yes  ⟨ `ℕ , ⊢N ⟩    =  no (λ { ⟨ _ , ⊢proj₂ ⊢N′ ⟩ → ℕ≢x (uniq-↑ ⊢N ⊢N′)}  )
  ... | yes ⟨ A ⇒ B , ⊢N ⟩  =  no (λ { ⟨ _ , ⊢proj₂ ⊢N′ ⟩ → x≢⇒ (uniq-↑ ⊢N ⊢N′)}  )
  ... | yes ⟨ A `× B , ⊢N ⟩  =  yes ⟨ B , ⊢proj₂ ⊢N ⟩

  inherit Γ (ƛ x ⇒ N) `ℕ      =  no  (λ())
  inherit Γ (ƛ x ⇒ N) (A ⇒ B) with inherit (Γ , x ⦂ A) N B
  ... | no ¬⊢N                =  no  (λ{ (⊢ƛ ⊢N)  →  ¬⊢N ⊢N })
  ... | yes ⊢N                =  yes (⊢ƛ ⊢N)
  inherit Γ `zero `ℕ          =  yes ⊢zero
  inherit Γ `zero (A ⇒ B)     =  no  (λ())
  inherit Γ (`suc M) `ℕ with inherit Γ M `ℕ
  ... | no ¬⊢M                =  no  (λ{ (⊢suc ⊢M)  →  ¬⊢M ⊢M })
  ... | yes ⊢M                =  yes (⊢suc ⊢M)
  inherit Γ (`suc M) (A ⇒ B)  =  no  (λ())
  inherit Γ (`case L [zero⇒ M |suc x ⇒ N ]) A with synthesize Γ L
  ... | no ¬∃                 =  no  (λ{ (⊢case ⊢L  _ _) → ¬∃ ⟨ `ℕ , ⊢L ⟩})
  ... | yes ⟨ A `× B ,  ⊢L  ⟩    = no (λ{ (⊢case ⊢L′  _ _) → ℕ≢x (uniq-↑ ⊢L′ ⊢L)})
  ... | yes ⟨ _ ⇒ _ , ⊢L ⟩    =  no  (λ{ (⊢case ⊢L′ _ _) → ℕ≢⇒ (uniq-↑ ⊢L′ ⊢L) })
  ... | yes ⟨ `ℕ ,    ⊢L ⟩ with inherit Γ M A
  ...    | no ¬⊢M             =  no  (λ{ (⊢case _ ⊢M _) → ¬⊢M ⊢M })
  ...    | yes ⊢M with inherit (Γ , x ⦂ `ℕ) N A
  ...       | no ¬⊢N          =  no  (λ{ (⊢case _ _ ⊢N) → ¬⊢N ⊢N })
  ...       | yes ⊢N          =  yes (⊢case ⊢L ⊢M ⊢N)
  inherit Γ (μ x ⇒ N) A with inherit (Γ , x ⦂ A) N A
  ... | no ¬⊢N                =  no  (λ{ (⊢μ ⊢N) → ¬⊢N ⊢N })
  ... | yes ⊢N                =  yes (⊢μ ⊢N)
  inherit Γ (M ↑) B with synthesize Γ M
  ... | no  ¬∃                =  no  (λ{ (⊢↑ ⊢M _) → ¬∃ ⟨ _ , ⊢M ⟩ })
  ... | yes ⟨ A , ⊢M ⟩ with A ≟Tp B
  ...   | no  A≢B             =  no  (¬switch ⊢M A≢B)
  ...   | yes A≡B             =  yes (⊢↑ ⊢M A≡B)
  inherit Γ `⟨ M , N ⟩ `ℕ = no  (λ())
  inherit Γ (ƛ x ⇒ M) (A `× B) = no  (λ())
  inherit Γ `zero  (A `× B) =  no  (λ())
  inherit Γ (`suc M) (A `× B) = no (λ())
  inherit Γ `⟨ M , N ⟩ (A ⇒ B) = no (λ())
  inherit Γ `⟨ M , N ⟩ (A `× B) with inherit Γ M A | inherit Γ N B
  ... | yes ⊢M | yes ⊢N = yes (`⟨ ⊢M , ⊢N ⟩)
  ... | yes ⊢M | no ¬⊢N = no (λ { `⟨ ⊢M , ⊢N ⟩ → ¬⊢N ⊢N })
  ... | no ¬⊢M | yes ⊢N = no (λ { `⟨ ⊢M , ⊢N ⟩ → ¬⊢M ⊢M })
  ... | no ¬⊢M | no ¬⊢N =  no (λ { `⟨ ⊢M , ⊢N ⟩ → ¬⊢N ⊢N })
  
  S′ : ∀ {Γ x y A B}
    → {x≢y : False (x ≟ y)}
    → Γ ∋ x ⦂ A
      ------------------
    → Γ , y ⦂ B ∋ x ⦂ A

  S′ {x≢y = x≢y} x = S (toWitnessFalse x≢y) x

  ∥_∥Tp : Type → DB.Type
  ∥ `ℕ ∥Tp             =  DB.`ℕ
  ∥ A ⇒ B ∥Tp          =  ∥ A ∥Tp DB.⇒ ∥ B ∥Tp
  ∥ A `× B ∥Tp         = ∥ A ∥Tp DB.`× ∥ B ∥Tp


  ∥_∥Cx : Context → DB.Context
  ∥ ∅ ∥Cx              =  DB.∅
  ∥ Γ , x ⦂ A ∥Cx      =  ∥ Γ ∥Cx DB., ∥ A ∥Tp


  ∥_∥∋ : ∀ {Γ x A} → Γ ∋ x ⦂ A → ∥ Γ ∥Cx DB.∋ ∥ A ∥Tp
  ∥ Z ∥∋               =  DB.Z
  ∥ S x≢ ∋x ∥∋         =  DB.S ∥ ∋x ∥∋

  ∥_∥⁺ : ∀ {Γ M A} → Γ ⊢ M ↑ A → ∥ Γ ∥Cx DB.⊢ ∥ A ∥Tp
  ∥_∥⁻ : ∀ {Γ M A} → Γ ⊢ M ↓ A → ∥ Γ ∥Cx DB.⊢ ∥ A ∥Tp

  ∥ ⊢` ⊢x ∥⁺           =  DB.` ∥ ⊢x ∥∋
  ∥ ⊢L · ⊢M ∥⁺         =  ∥ ⊢L ∥⁺ DB.· ∥ ⊢M ∥⁻
  ∥ ⊢↓ ⊢M ∥⁺           =  ∥ ⊢M ∥⁻
  ∥ ⊢proj₁ M  ∥⁺       = DB.`proj₁ ∥ M ∥⁺
  ∥ ⊢proj₂ N  ∥⁺       = DB.`proj₂ ∥ N ∥⁺

  ∥ ⊢ƛ ⊢N ∥⁻           =  DB.ƛ ∥ ⊢N ∥⁻
  ∥ ⊢zero ∥⁻           =  DB.`zero
  ∥ ⊢suc ⊢M ∥⁻         =  DB.`suc ∥ ⊢M ∥⁻
  ∥ ⊢case ⊢L ⊢M ⊢N ∥⁻  =  DB.case ∥ ⊢L ∥⁺ ∥ ⊢M ∥⁻ ∥ ⊢N ∥⁻
  ∥ ⊢μ ⊢M ∥⁻           =  DB.μ ∥ ⊢M ∥⁻
  ∥ ⊢↑ ⊢M refl ∥⁻      =  ∥ ⊢M ∥⁺

  ∥ `⟨ M , N ⟩ ∥⁻       = DB.`⟨ ∥ M ∥⁻ , ∥ N ∥⁻ ⟩
  
 ```
#### Exercise `inference-multiplication` (recommended)

Apply inference to your decorated definition of multiplication from
exercise [`bidirectional-mul`](/Inference/#bidirectional-mul), and show that
erasure of the inferred typing yields your definition of
multiplication from Chapter [DeBruijn](/DeBruijn/).

```agda
  ⊢mul : ∅ ⊢ mul ↑ `ℕ ⇒ `ℕ ⇒ `ℕ
  ⊢mul = 
   (⊢↓
      (⊢μ
       (⊢ƛ
        (⊢ƛ
         (⊢case
          (⊢`
           (S′ Z))
          ⊢zero
          (⊢↑
           (⊢↓
            (⊢μ
             (⊢ƛ
              (⊢ƛ
               (⊢case
                (⊢`
                 (S′ Z))
                (⊢↑ (⊢` Z) refl)
                (⊢suc
                 (⊢↑
                  (⊢`
                   (S′ (S′ (S′ Z)))
                   · ⊢↑ (⊢` Z) refl
                   ·
                   ⊢↑
                   (⊢`
                    (S′ Z))
                   refl)
                  refl))))))
            ·
            ⊢↑
            (⊢`
             (S′ Z))
            refl
            ·
            ⊢↑
            (⊢`
             (S′ (S′ (S′ Z)))
             · ⊢↑ (⊢` Z) refl
             ·
             ⊢↑
             (⊢`
              (S′ Z))
             refl)
            refl)
           refl))))))
  _ : synthesize ∅ mul ≡ yes ⟨ `ℕ ⇒ `ℕ ⇒ `ℕ , ⊢mul ⟩
  _ = refl

  DB-mul : ∀ {Γ} → Γ DB.⊢ DB.`ℕ DB.⇒ DB.`ℕ DB.⇒ DB.`ℕ
  DB-mul = DB.μ DB.ƛ DB.ƛ (DB.case (DB.# 1) DB.`zero (DB.plus DB.· (DB.# 1) DB.· (DB.# 3 DB.· DB.# 0 DB.· DB.# 1)))
  mul-erase : ∥ ⊢mul ∥⁺ ≡ DB-mul
  mul-erase = refl
```

#### Exercise `inference-products` (recommended)

Using your rules from exercise
[`bidirectional-products`](/Inference/#bidirectional-products), extend
bidirectional inference to include products.

```agda
  
  -- all the required solutions are written above.
  
```

#### Exercise `inference-rest` (stretch)

Extend the bidirectional type rules to include the rest of the constructs from
Chapter [More](/More/).

```agda
  -- Your code goes here
```



## Untyped

```
module Untyped where
```

## Imports

```agda
  import Relation.Binary.PropositionalEquality as Eq
  open Eq using (_≡_; refl; sym; trans; cong)
  open import Data.Empty using (⊥; ⊥-elim)
  open import Data.Nat using (ℕ; zero; suc; _+_; _∸_)
  open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
  open import Data.Unit using (⊤; tt)
  open import Function using (_∘_)
  open import Function.Equivalence using (_⇔_; equivalence)
  open import Relation.Nullary using (¬_; Dec; yes; no)
  open import Relation.Nullary.Decidable using (map)
  open import Relation.Nullary.Negation using (contraposition)
  open import Relation.Nullary.Product using (_×-dec_)
```


```
  open import plfa.part2.Untyped
    hiding ()
```

#### Exercise (`Type≃⊤`) (practice)

Show that `Type` is isomorphic to `⊤`, the unit type.

```agda
  -- Your code goes here
```

#### Exercise (`Context≃ℕ`) (practice)

Show that `Context` is isomorphic to `ℕ`.

```agda
  -- Your code goes here
```

#### Exercise (`variant-1`) (practice)

How would the rules change if we want call-by-value where terms
normalise completely?  Assume that `β` should not permit reduction
unless both terms are in normal form.

```agda
  -- Your code goes here
```

#### Exercise (`variant-2`) (practice)

How would the rules change if we want call-by-value where terms
do not reduce underneath lambda?  Assume that `β`
permits reduction when both terms are values (that is, lambda
abstractions).  What would `2+2ᶜ` reduce to in this case?

```agda
  -- Your code goes here
```


#### Exercise `plus-eval` (practice)

Use the evaluator to confirm that `plus · two · two` and `four`
normalise to the same term.

```agda
  -- Your code goes here
```

#### Exercise `multiplication-untyped` (recommended)

Use the encodings above to translate your definition of
multiplication from previous chapters with the Scott
representation and the encoding of the fixpoint operator.
Confirm that two times two is four.

```agda
  mul : ∀ {Γ} → Γ ⊢ ★ 
  mul = ƛ ƛ ƛ ƛ ( # 3 · ( # 2 · # 1  ) · # 0   ) 
  
  2*2ᶜ : ∅ ⊢ ★
  2*2ᶜ = mul · twoᶜ · twoᶜ 

  mul-test : eval (gas 30) 2*2ᶜ ≡ 
    steps
      ((ƛ    
        (ƛ
        (ƛ (ƛ (` (S (S (S Z)))) · ((` (S (S Z))) · (` (S Z))) · (` Z)))))
      · (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z))))
      · (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z))))
      —→⟨ ξ₁ β ⟩
      (ƛ
        (ƛ
        (ƛ
          (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) ·
          ((` (S (S Z))) · (` (S Z)))
          · (` Z))))
      · (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z))))
      —→⟨ β ⟩
      ƛ
      (ƛ
        (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) ·
        ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)))
        · (` Z))
      —→⟨ ζ (ζ (ξ₁ β)) ⟩
      ƛ
      (ƛ
        (ƛ
        (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S (S Z))) ·
        ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S (S Z))) · (` Z)))
        · (` Z))
      —→⟨ ζ (ζ β) ⟩
      ƛ
      (ƛ
        (ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) ·
        ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) · (` Z)))
      —→⟨ ζ (ζ (ξ₁ β)) ⟩
      ƛ
      (ƛ
        (ƛ (` (S (S Z))) · ((` (S (S Z))) · (` Z))) ·
        ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) · (` Z)))
      —→⟨ ζ (ζ β) ⟩
      ƛ
      (ƛ
        (` (S Z)) ·
        ((` (S Z)) ·
        ((ƛ (ƛ (` (S Z)) · ((` (S Z)) · (` Z)))) · (` (S Z)) · (` Z))))
      —→⟨ ζ (ζ (ξ₂ (ξ₂ (ξ₁ β)))) ⟩
      ƛ
      (ƛ
        (` (S Z)) ·
        ((` (S Z)) ·
        ((ƛ (` (S (S Z))) · ((` (S (S Z))) · (` Z))) · (` Z))))
      —→⟨ ζ (ζ (ξ₂ (ξ₂ β))) ⟩
      ƛ (ƛ (` (S Z)) · ((` (S Z)) · ((` (S Z)) · ((` (S Z)) · (` Z)))))
      ∎)
      (done
      (ƛ
        (ƛ
        (′
          (` (S Z)) ·
          (′ (` (S Z)) · (′ (` (S Z)) · (′ (` (S Z)) · (′ (` Z)))))))))
  mul-test = refl

```

#### Exercise `encode-more` (stretch)

Along the lines above, encode all of the constructs of
Chapter [More](/More/),
save for primitive numbers, in the untyped lambda calculus.

```agda
  -- Your code goes here
```
