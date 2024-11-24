-- BOTH:
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

/- TEXT:
.. _proving_identities_in_algebraic_structures:

证明代数结构中的恒等式
------------------------------------------

.. index:: ring (algebraic structure)

从数学上讲，一个环由一组对象 :math:`R`、运算 :math:`+`、:math:`\times` 和常数 :math:`0` 和 :math:`1`，以及一个操作 :math:`x \mapsto -x` 构成，且满足以下条件：

* :math:`R` 与 :math:`+` 构成一个 *阿贝尔群*，其中 :math:`0` 是加法单位元，负数是逆元。
* 乘法是结合的，具有单位元 :math:`1`，并且乘法对加法满足分配律。

在 Lean 中，对象的集合被表示为一个 *类型* ``R``. 环的公理如下：
TEXT. -/
section
-- QUOTE:
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
-- QUOTE.

end

/- TEXT:
关于第一行中的方括号，你稍后会了解更多，但暂且可以说，这个声明给了我们一个类型 ``R``，以及 ``R`` 上的一个环结构。
然后，Lean 允许我们使用一般的环定义以及 ``R`` 中的元素，并引用一个关于环的定理库。

一些定理的名称可能会令人感到熟悉：它们正是我们在上一节中用来进行实数计算的定理。
Lean 不仅适用于证明关于具体数学结构（如自然数和整数）的事实，还适用于证明关于抽象结构（例如环）的事实，这些抽象结构可以通过公理来刻画。
此外，Lean 支持对抽象和具体结构进行 *通用推理*，并且可以被训练用于识别适当的实例。
因此，关于环的任何定理都可以应用于具体的环，如整数 ``ℤ``、有理数 ``ℚ`` 和复数 ``ℂ``，也可以应用于扩展环的抽象结构的任何实例，例如任何有序环或任何域。

.. index:: commutative ring

然而，这并不是说实数的所有重要性质在任意环中都成立。
例如，实数上的乘法是交换的，但这对一般的环并不成立。
如果你曾学过线性代数课程，你会意识到，对于每个 :math:`n`，由实数组成的 :math:`n` 乘 :math:`n` 的矩阵形成一个环，在这个环中通常不满足交换性质。
事实上，如果我们声明 ``R`` 是一个 *交换* 环，则在用 ``R`` 替换 ``ℝ`` 时上一节中的所有定理仍然成立。
TEXT. -/
section
-- QUOTE:
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
-- QUOTE.

end

/- TEXT:
我们把检查其余证明的过程都不变的任务留给你。
注意，当一个证明很简短时，比如 ``by ring`` 或 ``by linarith`` 或 ``by sorry``，将其放在与 ``by`` 同一行上是常见的（也是允许的）。
良好的证明写作风格应该在简洁性和可读性之间取得平衡。

本节的目标是加强你在上一节中所发展的技能，并将它们应用于对环进行公理推理。
我们将从上面列出的公理开始，利用它们推导出其他事实。
我们证明的大部分事实已经在 Mathlib 中了。
我们将对这些事实在我们证明的版本中赋予相同的名称，以帮助你学习库的内容以及命名惯例。

.. index:: namespace, open, command ; open

Lean 提供了与编程语言类似的组织机制：当一个定义或定理 ``foo`` 被引入到 *命名空间* ``bar`` 中时，它的完整名称是 ``bar.foo``. 
稍后的命令 ``open bar`` 会 *打开* 这个命名空间，这样我们就可以使用更短的名称 ``foo``. 
为了避免由于名称冲突而产生的错误，在下一个示例中，我们将我们的库定理版本放在一个名为 ``MyRing`` 的新命名空间中。

下一个示例显示，我们不需要环公理 ``add_zero`` 或 ``add_right_neg``，因为它们可以由其他公理推导出来。
TEXT. -/
-- QUOTE:
namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing
-- QUOTE.

/- TEXT:
这样做的效果是，我们可以临时重新证明库中的定理，然后在那之后继续使用库中的版本。但是不要作弊！在接下来的练习中，请注意只使用我们在本节前面证明的关于环的一般事实。

（如果你注意到了，我们已经将 ``(R : Type*)`` 中的圆括号改为了 ``{R : Type*}`` 中的花括号。这声明了 ``R`` 是一个 *隐式参数*。我们将在稍后解释这意味着什么，但在现阶段不用担心它。）

下面是一个有用的定理：
TEXT. -/
-- BOTH:
namespace MyRing
variable {R : Type*} [Ring R]

-- EXAMPLES:
-- QUOTE:
theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]
-- QUOTE.

/- TEXT:
证明相伴的版本：
TEXT. -/
-- Prove these:
-- QUOTE:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem add_neg_cancel_rightαα (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_right_neg, add_zero]

/- TEXT:
利用这些来证明以下定理：
TEXT. -/
-- QUOTE:
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  sorry

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem add_left_cancelαα {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← neg_add_cancel_left a b, h, neg_add_cancel_left]

theorem add_right_cancelαα {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_neg_cancel_right a b, h, add_neg_cancel_right]

/- TEXT:
只要有足够的计划，你可以使用三次重写来证明每个定理。

.. index:: implicit argument

现在我们来解释一下花括号的用法。
假设你处于这样一种情况，在你的上下文中有 ``a``、 ``b`` 和 ``c``，以及一个假设 ``h : a + b = a + c``，
你想要得出结论 ``b = c``. 在 Lean 中，你可以将定理应用于假设和事实，就像你可以将它们应用于对象一样，因此你可能认为 ``add_left_cancel a b c h`` 是事实 ``b = c`` 的一个证明。
但请注意，明确地写出 ``a``、 ``b`` 和 ``c`` 是多余的，因为假设 ``h`` 明确指出了我们所关注的对象。
在这种情况下，输入一些额外的字符并不困难，但如果我们想将 ``add_left_cancel`` 应用于更复杂的表达式，写起来将会很繁琐。
在这种情况下，Lean 允许我们将参数标记为 *隐式的*，意味着它们应该被省略，并由其他方法推断出来，比如通过后续的参数和假设。
在 ``{a b c : R}`` 中的花括号就是这样做的。
因此，根据上面定理的陈述，正确的表达方式就是简单地写成 ``add_left_cancel h``. 

为了说明，让我们展示如何从环公理中推导出 ``a * 0 = 0``. 
TEXT. -/
-- QUOTE:
theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]
-- QUOTE.

/- TEXT:
.. index:: have, tactics ; have

我们使用了一个新技巧！
如果你逐步观察证明，你就可以看到发生了什么。
``have`` 策略引入了一个新的目标，即 ``a * 0 + a * 0 = a * 0 + 0``，它与原始目标具有相同的上下文。
下一行被缩进的事实表明，Lean 正在期待一个策略块来证明这个新目标。
因此，缩进鼓励一种模块化的证明风格：缩进的子证明构建了由 ``have`` 引入的目标。
在此之后，我们回到了证明原始目标的过程中，只是添加了一个新的假设 ``h``：一旦证明了它，我们现在就可以自由地使用它。
在这个位置，最终目标正是 ``add_left_cancel h`` 的结果。

.. index:: apply, tactics ; apply, exact, tactics ; exact

我们同样可以用 ``apply add_left_cancel h`` 或 ``exact add_left_cancel h`` 来结束证明。
``exact`` 策略接受一个完全证明当前目标的证明项作为参数，而不会创建任何新的目标。 ``apply`` 策略是一个变种，其参数不一定是一个完整的证明。
缺失的部分要么由 Lean 自动推断，要么成为要证明的新目标。
虽然 ``exact`` 策略在技术上是多余的，因为它比 ``apply`` 更弱，但它略微使证明脚本对人类读者更清晰，并且在库升级时更易于维护。

请记住，乘法并不被假设为可交换的，因此下面的定理也需要一些工作。
TEXT. -/
-- QUOTE:
theorem zero_mul (a : R) : 0 * a = 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem zero_mulαα (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by rw [← add_mul, add_zero, add_zero]
  rw [add_left_cancel h]

/- TEXT:
到现在，你应该也能够在下一个练习中用证明替换每个 ``sorry``，仍然只使用我们在本节中建立的关于环的事实。
TEXT. -/
-- QUOTE:
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  sorry

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  sorry

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem neg_eq_of_add_eq_zeroαα {a b : R} (h : a + b = 0) : -a = b := by
  rw [← neg_add_cancel_left a b, h, add_zero]

theorem eq_neg_of_add_eq_zeroαα {a b : R} (h : a + b = 0) : a = -b := by
  symm
  apply neg_eq_of_add_eq_zero
  rw [add_comm, h]

theorem neg_zeroαα : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_negαα (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  rw [neg_add_cancel]

-- BOTH:
end MyRing

/- TEXT:
在第三个定理中，我们不得不使用注释 ``(-0 : R)`` 而不是 ``0``，因为没有指定 ``R``，Lean 无法推断我们想要使用的是哪个 ``0``，默认情况下它将被解释为一个自然数。

在 Lean 中，可以证明环中减去一个元素等于加上它的加法逆元。
TEXT. -/
-- Examples.
section
variable {R : Type*} [Ring R]

-- QUOTE:
example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b
-- QUOTE.

end

/- TEXT:
在实数上，减法就是这样 *定义* 的：
TEXT. -/
-- QUOTE:
example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl
-- QUOTE.

/- TEXT:
.. index:: rfl, reflexivity, tactics ; refl and reflexivity, definitional equality

证明项 ``rfl`` 是“自反性”的简写。将它作为 ``a - b = a + -b`` 的证明，迫使 Lean 展开定义并识别出两边相同。 
``rfl`` 策略也是如此。这是 Lean 底层逻辑中已知的一种*定义等式*的实例。这意味着不仅可以使用 ``sub_eq_add_neg`` 进行重写，
以替换 ``a - b = a + -b``，而且在某些上下文中，处理实数时，你可以互换等式的两边。例如，你现在有足够的信息来证明上一节中的定理 ``self_sub``：
TEXT. -/
-- BOTH:
namespace MyRing
variable {R : Type*} [Ring R]

-- EXAMPLES:
-- QUOTE:
theorem self_sub (a : R) : a - a = 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_add_neg, add_right_neg]

/- TEXT:
展示你可以使用 ``rw`` 来证明这一点，但如果你将任意环 ``R`` 替换为实数，则还可以使用 ``apply`` 或 ``exact`` 来证明它。

Lean 知道在任何环中 ``1 + 1 = 2`` 都成立。通过一点努力，你可以利用这一点来证明上一节中的定理``two_mul``：
TEXT. -/
-- QUOTE:
-- BOTH:
theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

-- EXAMPLES:
theorem two_mul (a : R) : 2 * a = a + a := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem two_mulαα (a : R) : 2 * a = a + a := by
  rw [← one_add_one_eq_two, add_mul, one_mul]

-- BOTH:
end MyRing

/- TEXT:
.. index:: group (algebraic structure)

在本节结尾，我们注意到，我们上面建立的关于加法和负号的一些事实并不需要完整的环公理，甚至不需要加法的可交换性。弱一些的 *群* 的概念可以被公理化如下：
TEXT. -/
section
-- QUOTE:
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (neg_add_cancel : ∀ a : A, -a + a = 0)
-- QUOTE.

end

/- TEXT:
当群运算是可交换的时，惯例上使用加法符号，否则使用乘法符号。因此，Lean 定义了一个乘法版本以及一个加法版本（还有它们的阿贝尔变体，``AddCommGroup`` 和 ``CommGroup``）。
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {G : Type*} [Group G]

-- EXAMPLES:
#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)
-- QUOTE.

/- TEXT:
如果你感到自信，尝试使用这些公理来证明关于群的以下事实。你将需要在途中证明一些辅助引理。我们在本节中进行的证明提供了一些提示。
TEXT. -/
-- BOTH:
namespace MyGroup

-- EXAMPLES:
-- QUOTE:
theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
  sorry

theorem mul_one (a : G) : a * 1 = a := by
  sorry

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem mul_inv_cancelαα (a : G) : a * a⁻¹ = 1 := by
  have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
    rw [mul_assoc, ← mul_assoc a⁻¹ a, inv_mul_cancel, one_mul, inv_mul_cancel]
  rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]

theorem mul_oneαα (a : G) : a * 1 = a := by
  rw [← inv_mul_cancel a, ← mul_assoc, mul_inv_cancel, one_mul]

theorem mul_inv_revαα (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  rw [← one_mul (b⁻¹ * a⁻¹), ← inv_mul_cancel (a * b), mul_assoc, mul_assoc, ← mul_assoc b b⁻¹,
    mul_inv_cancel, one_mul, mul_inv_cancel, mul_one]

-- BOTH:
end MyGroup

end

/- TEXT:
.. index:: group (tactic), tactics ; group, tactics ; noncomm_ring, tactics ; abel

显式调用这些引理会很繁琐，因此 Mathlib 提供了类似于 `ring` 的策略来涵盖大多数用例： 
`group` 用于非交换的乘法群， `abel` 用于阿贝尔的加法群， `noncomm_ring` 用于非交换环。
可能看起来有些奇怪，代数结构被称为 `Ring` 和 `CommRing`，而策略被命名为 `noncomm_ring` 和 `ring`. 
这在一定程度上是出于历史原因，但也是为了方便使用更短的名称来表示处理交换环的策略，因为它使用得更频繁。
TEXT. -/
