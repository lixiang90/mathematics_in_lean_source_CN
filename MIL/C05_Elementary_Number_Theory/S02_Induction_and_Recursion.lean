import Mathlib.Data.Nat.GCD.Basic
import MIL.Common

/- TEXT:
.. _section_induction_and_recursion:

归纳和递归
-----------------------

自然数集 :math:`\mathbb{N} = \{ 0, 1, 2, \ldots \}`
不仅仅在自身意义下具有基本的重要性，
也在构造新数学对象中扮演着中心角色。
Lean 底层允许我们声明 *归纳类型*，
它是由一个给定的 *构造器* 列表归纳地生成的类型。
在 Lean 中，自然数声明如下。
OMIT: -/
namespace hidden

-- QUOTE:
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
-- QUOTE.

end hidden

/- TEXT:
你可以通过输入 ``#check Nat`` 然后在标识符 ``Nat`` 上使用 ``ctrl-click``
在库中找到这个声明。
这个命令指出 ``Nat`` 是由两个构造器 ``zero : Nat``
和 ``succ : Nat → Nat`` 自由而归纳地生成的数据类型。
当然，库中引入了记号 ``ℕ`` 和 ``0`` 以分别表示 ``nat`` 和 ``zero``.
（数字被转化为二进制表示，但我们现在不必担心这些细节。）

对于当代数学家来说，“自由”意味着类型
``Nat`` 有一个元素 ``zero`` 和一个单射后继函数
``succ``, 其像不包含 ``zero``.
EXAMPLES: -/
-- QUOTE:
example (n : Nat) : n.succ ≠ Nat.zero :=
  Nat.succ_ne_zero n

example (m n : Nat) (h : m.succ = n.succ) : m = n :=
  Nat.succ.inj h
-- QUOTE.

/- TEXT:
对于当代数学家来说，
“归纳地”一词意味着自然数具有归纳证明法则和递归定义法则。
本节将展示如何运用这些法则。

这是一个阶乘函数的递归定义的示例。
BOTH: -/
-- QUOTE:
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n
-- QUOTE.

/- TEXT:
该语法需要一些时间来适应。
请注意，第一行没有 ``:=``.
接下来的两行提供了基本情形和归纳步骤用于递归定义。
这些等式在定义上成立，
但它们也可以通过将名字 ``fac`` 送入 ``simp`` 或 ``rw`` 来手动使用。
EXAMPLES: -/
-- QUOTE:
example : fac 0 = 1 :=
  rfl

example : fac 0 = 1 := by
  rw [fac]

example : fac 0 = 1 := by
  simp [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n :=
  rfl

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  rw [fac]

example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
  simp [fac]
-- QUOTE.

/- TEXT:
阶乘函数实际上已经在 Mathlib 中被定义为 ``Nat.factorial``.
再次提醒，你可以通过输入 ``#check Nat.factorial`` 并使用 ``ctrl-click`` 跳转到它。
出于说明目的，我们会在示例中继续使用 ``fac``.
``Nat.factorial`` 的定义前面的标注 ``@[simp]``
要求定义等式应被添加到化简器默认使用的恒等式数据库中。

归纳原理是说，我们要证明一个关于自然数的一般断言，
可以先证明该断言对 0 成立，
再证明只要它对自然数 :math:`n` 成立，
它就对 :math:`n + 1` 也成立。
因此下列证明中 ``induction' n with n ih``
这一行将产生两个目标：
第一个是证明 ``0 < fac 0``,
第二个是在附加假设 ``ih : 0 < fac n`` 的条件下证明
``0 < fac (n + 1)``.
短语 ``with n ih`` 用于为变量和归纳假设命名，
你可以为它们选择你想要的任何名字。
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
``induction`` 策略足够智能，
足以包含那些依赖于归纳变量，作为归纳假设的一部分的假设。
逐步考察下一个示例，看看发生了什么。
EXAMPLES: -/
-- QUOTE:
theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
  induction' n with n ih
  · exact absurd ipos (not_lt_of_ge ile)
  rw [fac]
  rcases Nat.of_le_succ ile with h | h
  · apply dvd_mul_of_dvd_right (ih h)
  rw [h]
  apply dvd_mul_right
-- QUOTE.

/- TEXT:
下面的例子提供了阶乘函数的一个粗略下界。
事实证明，从分情况证明开始更容易，
因此证明的剩余部分以 :math:`n = 1` 这一情况开始。
看看你是否可以使用 ``pow_succ`` 或 ``pow_succ'`` 通过归纳证明来完成论证。
BOTH: -/
-- QUOTE:
theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
  rcases n with _ | n
  · simp [fac]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · simp [fac]
  simp at *
  rw [pow_succ', fac]
  apply Nat.mul_le_mul _ ih
  repeat' apply Nat.succ_le_succ
  apply zero_le

-- BOTH:
-- QUOTE.
/- TEXT:
归纳法通常用于证明涉及有限的和与乘积的恒等式。
Mathlib 定义了表达式 ``Finset.sum s f``,
其中 ``s : Finset α`` 是 ``α`` 类型元素的有限集，
而 ``f`` 是 ``α`` 上定义的函数。
``f`` 的到达域可以是任何支持交换、结合的加法运算且含有零的类型。
如果你导入 ``Algebra.BigOperators.Basic``
并发出命令 ``open BigOperators``,
你可以使用更具暗示性的符号 ``Σ x in s, f x``.
当然，还有类似的有限乘积运算和符号。

我们将在下一节中讨论 ``Finset`` 类型和它支持的运算，
然后在一个后续章节中再次讨论。
现在，我们只会用到 ``Finset.range n``,
它是小于 ``n`` 的自然数的有限集。
BOTH: -/
section

-- QUOTE:
variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

-- EXAMPLES:
#check Finset.sum s f
#check Finset.prod s f

-- BOTH:
open BigOperators
open Finset

-- EXAMPLES:
example : s.sum f = ∑ x in s, f x :=
  rfl

example : s.prod f = ∏ x in s, f x :=
  rfl

example : (range n).sum f = ∑ x in range n, f x :=
  rfl

example : (range n).prod f = ∏ x in range n, f x :=
  rfl
-- QUOTE.

/- TEXT:
事实 ``Finset.sum_range_zero`` 和 ``Finset.sum_range_succ``
提供了一直加到 :math:`n` 的求和的递归描述，
乘积也类似。
EXAMPLES: -/
-- QUOTE:
example (f : ℕ → ℕ) : ∑ x in range 0, f x = 0 :=
  Finset.sum_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∑ x in range n.succ, f x = ∑ x in range n, f x + f n :=
  Finset.sum_range_succ f n

example (f : ℕ → ℕ) : ∏ x in range 0, f x = 1 :=
  Finset.prod_range_zero f

example (f : ℕ → ℕ) (n : ℕ) : ∏ x in range n.succ, f x = (∏ x in range n, f x) * f n :=
  Finset.prod_range_succ f n
-- QUOTE.

/- TEXT:
每对中的第一个恒等式是定义性成立的，也就是说，
你可以把证明替换为 ``rfl``.

下面把我们定义的阶乘函数表示为乘积。
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : fac n = ∏ i in range n, (i + 1) := by
  induction' n with n ih
  · simp [fac, prod_range_zero]
  simp [fac, ih, prod_range_succ, mul_comm]
-- QUOTE.

/- TEXT:
我们在简化规则中包含 ``mul_comm`` 这一事实值得讨论。
使用恒等式 ``x * y = y * x`` 进行简化似乎很危险，
这通常会无限循环。
Lean 的化简器足够智能，
只会在对于任意项的某个固定的序，
结果项具有较小的值时才会应用这一规则。
下面的示例演示使用三个规则
``mul_assoc``, ``mul_comm`` 和 ``mul_left_comm`` 进行化简，
从而识别除了括号的位置和变量的顺序以外相同的乘积。
EXAMPLES: -/
-- QUOTE:
example (a b c d e f : ℕ) : a * (b * c * f * (d * e)) = d * (a * f * e) * (c * b) := by
  simp [mul_assoc, mul_comm, mul_left_comm]
-- QUOTE.

/- TEXT:
粗略地说，规则的工作原理是将括号向右推，
然后对两边的表达式重新排序，
直到两者都遵循相同的规范顺序。
用这些规则，以及相应的加法规则来化简，是一个方便的技巧。

回到求和等式，我们建议一步步完成下面的证明，
即一直加到 :math:`n` （包括 :math:`n` 在内）的自然数之和为 :math:`n (n + 1) / 2`.
证明的第一步是去分母。
这在形式化等式时通常很有用，
因为除法计算一般都有附带条件。
(尽可能避免在自然数上使用减法也同样有用）。
EXAMPLES: -/
-- QUOTE:
theorem sum_id (n : ℕ) : ∑ i in range (n + 1), i = n * (n + 1) / 2 := by
  symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 2, ← ih]
  ring
-- QUOTE.

/- TEXT:
我们鼓励你证明平方和的类似等式，
以及你可以在网上找到的其他等式。
BOTH: -/
-- QUOTE:
theorem sum_sqr (n : ℕ) : ∑ i in range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  symm;
  apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 6)
  induction' n with n ih
  · simp
  rw [Finset.sum_range_succ, mul_add 6, ← ih]
  ring
-- QUOTE.

-- BOTH:
end

/- TEXT:
在 Lean 的核心库中，
加法和乘法本身就是通过递归定义的，
其基本性质是通过归纳法建立的。
如果你喜欢思考这样的基础话题，
那么你可能会喜欢研究乘法和加法的交换性和结合性，
以及乘法对加法的分配性的证明。
你可以按照下面的提纲，
在自然数的副本上进行证明。
请注意，我们可以对 ``MyNat`` 使用 ``induction`` 策略；
Lean 很聪明，知道使用相关的归纳法则
（当然，它与 ``Nat`` 的归纳法则相同）。

我们从加法的交换性开始。
一个很好的经验法则是，
由于加法和乘法是通过第二个参数上的递归来定义的，
所以一般来说，
通过对出现在该位置上的变量做归纳来进行证明是有利的。
在结合性证明中决定使用哪个变量有点技巧性。

如果不使用通常的符号来表示零、一、加法和乘法，
书写起来会很混乱。
我们稍后将学习如何定义这种符号。
在命名空间 ``MyNat`` 中工作意味着我们可以编写
``zero`` 和 ``succ`` 而不是 ``MyNat.zero`` 和 ``MyNat.succ``,
而且这些名字解释优先于其他解释。
在命名空间之外，例如，下面定义的 ``add`` 的全名是 ``MyNat.add``.

如果你发现自己 *真的* 喜欢这类问题，
可以尝试定义截断减法和指数运算，并证明它们的一些性质。
请记住，截断减法的终点是零。
要定义截断减法，需要定义一个前继函数 ``pred``,
从任何非零数中减去一并保持零不变。
函数 ``pred`` 可以通过一个简单的递归实例来定义。
BOTH: -/
-- QUOTE:
inductive MyNat where
  | zero : MyNat
  | succ : MyNat → MyNat

namespace MyNat

def add : MyNat → MyNat → MyNat
  | x, zero => x
  | x, succ y => succ (add x y)

def mul : MyNat → MyNat → MyNat
  | x, zero => zero
  | x, succ y => add (mul x y) x

theorem zero_add (n : MyNat) : add zero n = n := by
  induction' n with n ih
  · rfl
  rw [add, ih]

theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
  induction' n with n ih
  · rfl
  rw [add, ih]
  rfl

theorem add_comm (m n : MyNat) : add m n = add n m := by
  induction' n with n ih
  · rw [zero_add]
    rfl
  rw [add, succ_add, ih]

theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' k with k ih
  · rfl
  rw [add, ih]
  rfl

-- BOTH:
theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' k with k ih
  · rfl
  rw [add, mul, mul, ih, add_assoc]

-- BOTH:
theorem zero_mul (n : MyNat) : mul zero n = zero := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · rfl
  rw [mul, ih]
  rfl

-- BOTH:
theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · rfl
  rw [mul, mul, ih, add_assoc, add_assoc, add_comm n, succ_add]
  rfl

-- BOTH:
theorem mul_comm (m n : MyNat) : mul m n = mul n m := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  induction' n with n ih
  · rw [zero_mul]
    rfl
  rw [mul, ih, succ_mul]

-- BOTH:
end MyNat
-- QUOTE.
