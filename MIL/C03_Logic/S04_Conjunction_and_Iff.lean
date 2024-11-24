-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace C03S04

/- TEXT:
.. _conjunction_and_biimplication:

合取和等价
-------------------

.. index:: constructor, tactics ; constructor

你已经看到，合取符号 ``∧`` 用于表示 "且"。
``constructor`` 策略允许你通过分别证明 ``A`` 和 ``B`` 证明形如 ``A ∧ B``
的定理。
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]
-- QUOTE.

/- TEXT:
.. index:: assumption, tactics ; assumption

在这个例子中， ``assumption`` 策略要求 Lean 寻找一个能解决目标的假设。
注意到最后的 ``rw`` 应用了 ``≤`` 的自反性以完成目标。
下面是解决前面的例子的其他一些方法，使用匿名构造器角括号。
第一个是前述证明熟练的证明项版本，在关键字 ``by`` 处落入策略模式。
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩
-- QUOTE.

/- TEXT:
*使用* 合取而不是证明合取，就需要拆开两部分的证明。
你可以用 ``rcases`` 策略做这个，
也可以使用 ``rintro`` 或一个模式匹配函数 ``fun``,
使用方式都与它们在存在量词中的使用方式类似。
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')
-- QUOTE.

/- TEXT:
就像 ``obtain`` 策略一样，还有一个模式匹配版的 ``have``:
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁
-- QUOTE.

/- TEXT:
和 ``rcases`` 相反，这里 ``have`` 策略把 ``h`` 留在了上下文中。
以及，我们又一次拥有了计算机科学家的模式匹配语法，尽管我们不会使用它们：
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁
-- QUOTE.

/- TEXT:
与使用存在量词不同，
你可以通过输入 ``h.left`` 和 ``h.right``,
或者，等价地， ``h.1`` 和 ``h.2``,
提取假设 ``h : A ∧ B`` 两部分的证明。
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')
-- QUOTE.

/- TEXT:
尝试使用这些技术，想出多种方式证明以下内容：
TEXT. -/
-- QUOTE:
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m := by
  rcases h with ⟨h0, h1⟩
  constructor
  · exact h0
  intro h2
  apply h1
  apply Nat.dvd_antisymm h0 h2

/- TEXT:
你可以通过匿名构造器 ``rintro`` 和 ``rcases`` 嵌套使用 ``∃`` 和 ``∧``.
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨z, xltz, zlty⟩ ↦ lt_trans xltz zlty
-- QUOTE.

/- TEXT:
你也可以使用 ``use`` 策略：
TEXT. -/
-- QUOTE:
example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')
-- QUOTE.

/- TEXT:
在第一个例子中， ``constructor`` 命令后的分号告诉 Lean 对产生的全部两个目标使用 ``norm_num`` 策略。

在 Lean 中， ``A ↔ B`` *并非* 定义为 ``(A → B) ∧ (B → A)``,
但其实如果这样定义也无妨，
而且它的行为几乎与此相同。
你已经看到，你可以输入 ``h.mp`` 和 ``h.mpr``,
或者 ``h.1`` 和 ``h.2``,
用于表示 ``h : A ↔ B`` 的两个方向。
你也可以使用 ``cases`` 及类似策略。
要证明一条当且仅当语句，
你可以使用 ``constructor`` 或角括号，
就像你要证明一个合取一样。
TEXT. -/
-- QUOTE:
example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩
-- QUOTE.

/- TEXT:
最后一个证明项令人费解。
请记住，在编写这样的表达式时，可以使用下划线来查看 Lean 的预期。

尝试你刚才学到的的各种技术和工具以证明下列命题：
TEXT. -/
-- QUOTE:
example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y := by
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · exact h0
    intro h2
    apply h1
    rw [h2]
  rintro ⟨h0, h1⟩
  constructor
  · exact h0
  intro h2
  apply h1
  apply le_antisymm h0 h2

/- TEXT:
这是一个更有意思的练习，请证明，对于任意两个实数 ``x`` 和 ``y``,
``x^2 + y^2 = 0`` 当且仅当 ``x = 0`` 且 ``y = 0``.
我们建议使用 ``linarith``, ``pow_two_nonneg`` 和 ``pow_eq_zero``
证明一条辅助性的引理。
TEXT. -/
-- QUOTE:
theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by sorry
  pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 :=
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem auxαα {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by linarith [pow_two_nonneg x, pow_two_nonneg y]
  pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · exact aux h
    rw [add_comm] at h
    exact aux h
  rintro ⟨rfl, rfl⟩
  norm_num

/- TEXT:
在 Lean 中，双向蕴含具有双重身份。
你可以将其视为合取，分别使用其两个部分。
但 Lean 也知道它是命题之间的一个反射、对称且传递的关系，
你也可以通过 ``calc`` 和 ``rw`` 使用它。
把一个语句重写为等价语句经常很方便。
在下一个例子中，我们使用 ``abs_lt`` 将形如 ``|x| < y``
的表达式替换为等价表达式 ``- y < x ∧ x < y``,
在下下个例子中，我们使用 ``Nat.dvd_gcd_iff``
将形如 ``m ∣ Nat.gcd n k`` 的表达式替换为等价表达式 ``m ∣ n ∧ m ∣ k``.
TEXT. -/
section

-- QUOTE:
example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num
-- QUOTE.

end

/- TEXT:
看看你能否将 ``rw`` 与下面的定理结合起来使用来简短地证明相反数不是一个非递减函数。
(注意 ``push_neg`` 不会为你展开定义，所以需要在定理证明中使用 ``rw [Monotone]``）。
BOTH: -/
-- QUOTE:
theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

-- EXAMPLES:
example : ¬Monotone fun x : ℝ ↦ -x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : ¬Monotone fun x : ℝ ↦ -x := by
  rw [not_monotone_iff]
  use 0, 1
  norm_num

/- TEXT:
本节其余练习题旨在为你提供关于合取和双向蕴含的进一步练习。
请记住，*偏序* 是一种具有传递性、反身性和反对称性的二元关系。
有时还会出现一个更弱的概念：*预序* 只是一个反身、传递关系。
对于任何预序 ``≤``,
Lean 把相应的严格预序公理化定义为
``a < b ↔ a ≤ b ∧ ¬ b ≤ a``.
证明如果 ``≤`` 是偏序，
那么 ``a < b`` 等价于 ``a ≤ b ∧ a ≠ b``:
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [PartialOrder α]
variable (a b : α)

-- EXAMPLES:
example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_le]
  sorry
-- QUOTE.

-- SOLUTIONS:
example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_le]
  constructor
  · rintro ⟨h0, h1⟩
    constructor
    · exact h0
    intro h2
    apply h1
    rw [h2]
  rintro ⟨h0, h1⟩
  constructor
  · exact h0
  intro h2
  apply h1
  apply le_antisymm h0 h2

-- BOTH:
end

/- TEXT:
.. index:: simp, tactics ; simp

除了逻辑运算以外，你不需要 ``le_refl`` 和 ``le_trans`` 之外的任何东西。
证明即使在只假定 ``≤`` 是预序的情况下，
我们也可以证明严格序是反自反的和传递的。
在第二个例子中，为了方便，
我们使用了化简器而非 ``rw`` 把 ``<`` 表示为关于 ``≤`` 和 ``¬``
的表达式。
我们稍后再讨论化简器，
但在这里，我们只依赖于这样一个事实：
它会重复使用指定的引理，
即使需要用不同的值将其实例化。
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [Preorder α]
variable (a b c : α)

-- EXAMPLES:
example : ¬a < a := by
  rw [lt_iff_le_not_le]
  sorry

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_le]
  sorry
-- QUOTE.

-- SOLUTIONS:
example : ¬a < a := by
  rw [lt_iff_le_not_le]
  rintro ⟨h0, h1⟩
  exact h1 h0

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_le]
  rintro ⟨h0, h1⟩ ⟨h2, h3⟩
  constructor
  · apply le_trans h0 h2
  intro h4
  apply h1
  apply le_trans h2 h4

-- BOTH:
end
