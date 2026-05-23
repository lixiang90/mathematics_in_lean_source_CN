import MIL.Common
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Data.Nat.GCD.Basic

namespace more_induction

/- TEXT:

.. _more_induction:

更多归纳
--------------

在 :numref:`section_induction_and_recursion` 中，我们看见了如何通过
对自然数进行递归来定义阶乘函数。
EXAMPLES: -/
-- QUOTE:
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n
-- QUOTE.

/- TEXT:
我们也看见了如何使用 ``induction'`` 策略来证明定理。
EXAMPLES: -/
-- QUOTE:
theorem fac_pos (n : ℕ) : 0 < fac n := by
  induction' n with n ih
  · rw [fac]
    exact zero_lt_one
  rw [fac]
  exact mul_pos n.succ_pos ih
-- QUOTE.

/- TEXT:
``induction`` 策略（不带撇号）允许更具结构化的语法。
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : 0 < fac n := by
  induction n
  case zero =>
    rw [fac]
    exact zero_lt_one
  case succ n ih =>
    rw [fac]
    exact mul_pos n.succ_pos ih

example (n : ℕ) : 0 < fac n := by
  induction n with
  | zero =>
    rw [fac]
    exact zero_lt_one
  | succ n ih =>
    rw [fac]
    exact mul_pos n.succ_pos ih
-- QUOTE.

/- TEXT:
像往常一样，你可以将鼠标悬停在 ``induction`` 关键字上以阅读文档。
情形 ``zero`` 和 ``succ`` 的名字取自类型 `ℕ` 的定义。
注意 ``succ`` 情形允许你为归纳变量和归纳假设
选择任何你想要的名字，这里分别是 ``n`` 和 ``ih``。
你甚至可以用与定义递归函数相同的记号来证明一个定理。
EXAMPLES: -/
-- QUOTE:
theorem fac_pos' : ∀ n, 0 < fac n
  | 0 => by
    rw [fac]
    exact zero_lt_one
  | n + 1 => by
    rw [fac]
    exact mul_pos n.succ_pos (fac_pos' n)
-- QUOTE.

/- TEXT:
还要注意这里没有 ``:=``，冒号后面没有 ``∀ n``，每种情形中没有 ``by`` 关键字，
以及归纳中调用了 ``fac_pos' n``。
这就好像这个定理是 ``n`` 的递归函数，而在归纳步骤中我们做了一个递归调用。

这种定义风格非常灵活。
Lean 的设计者们内置了精密的递归函数定义方法，而这些
方法也延伸到了用归纳法进行证明。
例如，我们可以用多个基本情形来定义斐波那契函数。
BOTH: -/
-- QUOTE:
@[simp] def fib : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)
-- QUOTE.

/- TEXT:
``@[simp]`` 标注意味着化简器会使用这些定义等式。
你也可以通过写 ``rw [fib]`` 来应用它们。
在下面，给 ``n + 2`` 的情形一个名字将会很有帮助。
BOTH: -/
-- QUOTE:
theorem fib_add_two (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := rfl

-- EXAMPLES:
example (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := by rw [fib]
-- QUOTE.

/- TEXT:
使用 Lean 的递归函数记号，你可以对自然数进行归纳证明，
这些证明反映了 ``fib`` 的递归定义。
下面的例子给出了第 n 个斐波那契数关于
黄金比例 ``φ`` 及其共轭 ``φ'`` 的显式公式。
我们必须告诉 Lean，我们不期望我们的定义生成代码，因为
实数上的算术运算是不可计算的。

EXAMPLES: -/
-- QUOTE:
noncomputable section

def phi  : ℝ := (1 + √5) / 2
def phi' : ℝ := (1 - √5) / 2

theorem fib_eq : ∀ n, fib n = (phi^n - phi'^n) / √5
  | 0   => by simp
  | 1   => by unfold fib; grind [phi, phi']
  | n+2 => by unfold fib; simp; grind [fib_eq n, fib_eq (n+1), phi, phi']

end
-- QUOTE.

/- TEXT:
涉及斐波那契函数的归纳证明不必是这种形式。
下面我们重现 ``Mathlib`` 中证明相邻斐波那契数互素的证明。
EXAMPLES: -/
-- QUOTE:
theorem fib_coprime_fib_succ (n : ℕ) : Nat.Coprime (fib n) (fib (n + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [fib, Nat.coprime_add_self_right]
    exact ih.symm
-- QUOTE.

/- TEXT:
利用 Lean 的计算解释，我们可以计算斐波那契数。
EXAMPLES: -/
-- QUOTE:
#eval fib 6
#eval List.range 20 |>.map fib
-- QUOTE.

/- TEXT:
``fib`` 的直接实现在计算上是低效的。事实上，它的运行时间
随其参数指数增长。（你应该想想为什么。）
在 Lean 中，我们可以实现下面的尾递归版本，其运行时间关于 ``n`` 是线性的，
并证明它计算的是同一个函数。
EXAMPLES: -/
-- QUOTE:
def fib' (n : Nat) : Nat :=
  aux n 0 1
where aux
  | 0,   x, _ => x
  | n+1, x, y => aux n y (x + y)

theorem fib'.aux_eq (m n : ℕ) : fib'.aux n (fib m) (fib (m + 1)) = fib (n + m) := by
  induction n generalizing m with
  | zero => simp [fib'.aux]
  | succ n ih => rw [fib'.aux, ←fib_add_two, ih, add_assoc, add_comm 1]

theorem fib'_eq_fib : fib' = fib := by
  ext n
  erw [fib', fib'.aux_eq 0 n]; rfl

#eval fib' 10000
-- QUOTE.

/- TEXT:
注意在 ``fib'.aux_eq`` 的证明中 ``generalizing`` 关键字的作用。
它用来在归纳假设前面插入一个 ``∀ m``，这样在归纳步骤中，
``m`` 可以取不同的值。
你可以逐步查看这个证明，并检验在这种情况下，量词需要在
归纳步骤中被实例化为 ``m + 1``。

还要注意使用 ``erw`` （表示“扩展重写”）而不是 ``rw``。
之所以使用它，是因为要重写目标 ``fib'.aux_eq``，需要把 ``fib 0`` 和 ``fib 1``
分别化简为 ``0`` 和 ``1``。
``erw`` 策略在展开定义以匹配参数方面比 ``rw`` 更激进。
这并不总是一个好主意；在某些情况下它会浪费大量时间，所以请谨慎使用 ``erw``。

下面是 ``generalizing`` 关键字在另一个 ``Mathlib`` 中的恒等式证明里的另一个例子。
该恒等式的一个非形式化证明可以在 `这里 <https://proofwiki.org/wiki/Fibonacci_Number_in_terms_of_Smaller_Fibonacci_Numbers>`_ 找到。
我们提供了形式化证明的两个变体。
BOTH: -/
-- QUOTE:
theorem fib_add (m n : ℕ) : fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    specialize ih (m + 1)
    rw [add_assoc m 1 n, add_comm 1 n] at ih
    simp only [fib_add_two, ih]
    ring

-- EXAMPLES:
theorem fib_add' : ∀ m n, fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1)
  | _, 0     => by simp
  | m, n + 1 => by
    have := fib_add' (m + 1) n
    rw [add_assoc m 1 n, add_comm 1 n] at this
    simp only [fib_add_two, this]
    ring
-- QUOTE.

/- TEXT:
作为练习，请使用 ``fib_add`` 来证明下面的结论。
BOTH: -/
-- QUOTE:
example (n : ℕ): (fib n) ^ 2 + (fib (n + 1)) ^ 2 = fib (2 * n + 1) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rw [two_mul, fib_add, pow_two, pow_two]
-- QUOTE.

/- TEXT:
Lean 定义递归函数的机制足够灵活，允许任意的
递归调用，只要参数的复杂度按照某种
良基测度下降。
在下一个例子中，我们证明每个自然数 ``n ≠ 1`` 都有一个素因子，
利用了如果 ``n`` 非零且不是素数，它就有更小的因子这一事实。
（你可以检查 Mathlib 在 ``Nat`` 命名空间中有一个同名的定理，
不过它的证明与我们这里给出的不同。）

EXAMPLES: -/
-- QUOTE:
#check (@Nat.not_prime_iff_exists_dvd_lt :
  ∀ {n : ℕ}, 2 ≤ n → (¬Nat.Prime n ↔ ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n))

theorem ne_one_iff_exists_prime_dvd : ∀ {n}, n ≠ 1 ↔ ∃ p : ℕ, p.Prime ∧ p ∣ n
  | 0 => by simpa using Exists.intro 2 Nat.prime_two
  | 1 => by simp [Nat.not_prime_one]
  | n + 2 => by
    have hn : n + 2 ≠ 1 := by omega
    simp only [Ne, not_false_iff, true_iff, hn]
    by_cases h : Nat.Prime (n + 2)
    · use n + 2, h
    · have : 2 ≤ n + 2 := by omega
      rw [Nat.not_prime_iff_exists_dvd_lt this] at h
      rcases h with ⟨m, mdvdn, mge2, -⟩
      have : m ≠ 1 := by omega
      rw [ne_one_iff_exists_prime_dvd] at this
      rcases this with ⟨p, primep, pdvdm⟩
      use p, primep
      exact pdvdm.trans mdvdn
-- QUOTE.

/- TEXT:
``rw [ne_one_iff_exists_prime_dvd] at this`` 这一行就像一个魔术：我们在
自己的证明中使用了我们正在证明的定理本身。
使它起作用的是归纳调用被实例化在 ``m`` 上，
当前情形是 ``n + 2``，而上下文中有 ``m < n + 2``。
Lean 可以找到这个假设并用它来证明归纳是良基的。
Lean 非常善于找出什么是递减的；在这种情况下，定理陈述中
``n`` 的选择以及小于关系是显而易见的。
在更复杂的情况下，Lean 提供了显式提供这一信息的机制。
请参阅 Lean 参考手册中关于 `良基递归 <https://lean-lang.org/doc/reference/latest//Definitions/Recursive-Definitions/#well-founded-recursion>`_ 的章节。

有时，在证明中，你需要根据自然数 ``n``
是零还是后继来分情况，而在后继情形中不需要归纳假设。
为此，你可以使用 ``cases`` 和 ``rcases`` 策略。
EXAMPLES: -/
-- QUOTE:
theorem zero_lt_of_mul_eq_one (m n : ℕ) : n * m = 1 → 0 < n ∧ 0 < m := by
  cases n <;> cases m <;> simp

example (m n : ℕ) : n*m = 1 → 0 < n ∧ 0 < m := by
  rcases m with (_ | m); simp
  rcases n with (_ | n) <;> simp
-- QUOTE.

/- TEXT:
这是一个有用的技巧。
经常你有一个关于自然数 ``n`` 的定理，其中零的情形很容易。
如果你对 ``n`` 进行分情况并迅速处理零的情形，
你就剩下了原来的目标，只不过 ``n`` 被替换成了 ``n + 1``。
EXAMPLES: -/
