import MIL.Common
import Mathlib.Data.Real.Basic
/- TEXT:
计算
-----------

通常我们学习数学计算时并不将其视为证明。
但是，当我们像Lean要求的那样验证计算中的每一步时，最终的结果就是一个证明，证明了算式的左侧等于右侧。

.. index:: rewrite, rw, tactics ; rw and rewrite

在Lean中，陈述一个定理等同于陈述一个目标，即证明该定理的目标。Lean 提供了重写策略 ``rw``，用于在目标中将等式的左侧替换为右侧。
如果 ``a``、 ``b`` 和 ``c`` 是实数，那么 ``mul_assoc a b c`` 是等式 ``a * b * c = a * (b * c)``, 
而 ``mul_comm a b`` 是等式 ``a * b = b * a``. Lean 提供了自动化工具，通常可以消除精确引用这类事实的必要性，但它们对于说明的目的很有用。
在Lean中，乘法左结合，因此 ``mul_assoc`` 的左侧也可以写成 ``(a * b) * c``. 然而，通常要注意Lean的记号约定，好的风格是在Lean省略括号时也这样做。

让我们尝试一下 ``rw``.

.. index:: real numbers
TEXT. -/
-- An example.
-- QUOTE:
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]
-- QUOTE.

/- TEXT:
在相关示例文件的开头的 ``import`` 行从 Mathlib 中导入了实数理论，以及有用的自动化功能。出于简洁起见，我们通常在教科书中删除此类信息。

欢迎你进行更改以观察发生了什么。你可以在 VS Code 中将 ``ℝ`` 字符输入为 ``\R`` 或 ``\real``. 
该符号直到你按下空格键或制表符键才会出现。当阅读 Lean 文件时，如果你将光标悬停在一个符号上，VS Code 将显示用于输入该符号的语法。
如果你想查看所有可用的缩写，可以按下 Ctrl-Shift-P，然后输入abbreviations来访问 ``Lean 4: Show all abbreviations`` 命令。
如果您的键盘上没有方便使用的反斜杠，可以通过更改 ``lean4.input.leader`` 设置来改变前导字符。

.. index:: proof state, local context, goal

当光标位于策略证明的中间时，Lean 会在 *Lean Infoview* 窗口中报告当前的 *证明状态*。
当你将光标移到证明的每一步时，你可以看到状态的变化。Lean 中的典型证明状态可能如下所示：

.. code-block::

    1 goal
    x y : ℕ,
    h₁ : Prime x,
    h₂ : ¬Even x,
    h₃ : y > x
    ⊢ y ≥ 4

在以 ``⊢`` 开头的行之前的行表示 *上下文*：它们是当前正在使用的对象和假设。
在这个例子中，它们包括两个对象， ``x`` 和 ``y``，每个都是自然数。
它们还包括三个假设，标记为 ``h₁``、 ``h₂`` 和 ``h₃``.
在Lean中，上下文中的所有内容都用标识符标记。你可以将这些带下标的标签键入为 ``h\1``、``h\2`` 和 ``h\3``,
但任何合法的标识符都可以：你可以使用 ``h1``、 ``h2``、 ``h3``，或者 ``foo``、 ``bar`` 和 ``baz``. 
最后一行代表 *目标(goal)*，即要证明的事实。有时人们使用 *目的(target)* 表示要证明的事实，使用 *目标(goal)* 表示上下文和目的(target)的组合。在实践中，意图通常是明确的。

尝试证明这些等式，在每种情况下都将 ``sorry`` 替换为策略证明。
使用 ``rw`` 策略时，你可以使用左箭头（``\l``）来反转一个等式。
例如，``rw [← mul_assoc a b c]`` 在当前目标中将 ``a * (b * c)`` 替换为 ``a * b * c``. 
请注意，左箭头指的是从右向左在 ``mul_assoc`` 提供的等式中进行，与目标的左侧或右侧无关。
TEXT. -/
-- Try these.
-- QUOTE:
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_comm c b]
  rw [mul_assoc b c a]
  rw [mul_comm c a]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc a b c]
  rw [mul_comm a b]
  rw [mul_assoc b a c]

/- TEXT:
你也可以在不带参数的情况下使用诸如 ``mul_assoc`` 和 ``mul_comm`` 这样的等式。
在这种情况下，重写策略会尝试使用它找到的第一个模式将等式左侧与目标中的表达式匹配。
TEXT. -/
-- An example.
-- QUOTE:
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]
-- QUOTE.

/- TEXT:
你还可以提供 *部分* 信息。例如， ``mul_comm a`` 匹配任何形式为 ``a * ?`` 的模式，并将其重写为 ``? * a``. 
尝试在不提供任何参数的情况下完成第一个示例，只使用一个参数完成第二个示例。
TEXT. -/
/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
-- QUOTE:
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a]
  rw [mul_assoc]

/- TEXT:
你也可以对局部上下文中的事实使用 ``rw`` 策略。
TEXT. -/
-- Using facts from the local context.
-- QUOTE:
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
-- QUOTE.

/- TEXT:
尝试下列问题，使用定理 ``sub_self`` 完成第二个：
TEXT. -/
-- QUOTE:
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a]
  rw [h]
  rw [← mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp]
  rw [hyp']
  rw [mul_comm]
  rw [sub_self]

/- TEXT:
通过在方括号内用逗号分隔列出相关的等式，可以一次性执行多个重写命令。
TEXT. -/
-- QUOTE:
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
-- QUOTE.

/- TEXT:
你仍然可以通过将光标放置在任何重写列表中逗号的后面，看到增量进展。

另一个技巧是，我们可以在示例或定理之外一次性声明变量。然后，Lean 就会自动包含这些变量。
TEXT. -/
section

-- QUOTE:
variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
-- QUOTE.

end

/- TEXT:
在上述证明开始时检查策略状态，可以看到 Lean 确实包含了所有变量。我们可以通过将其放置在一个 ``section ... end`` 块中来限定声明的范围。
最后，回想一下前言中提到的，Lean 为我们提供了一个命令来确定表达式的类型：
TEXT. -/
-- QUOTE:
section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end
-- QUOTE.

/- TEXT:
``#check`` 命令适用于对象和事实。对于命令 ``#check a``，Lean 报告 ``a`` 的类型为 ``ℝ``. 
对于命令 ``#check mul_comm a b``，Lean 报告 ``mul_comm a b`` 是一个证明了事实 ``a * b = b * a`` 的证明。
命令 ``#check (a : ℝ)`` 表示我们期望 ``a`` 的类型是 ``ℝ``，如果不是这样，Lean 将会抛出错误。
我们将在后面解释最后三个 ``#check`` 命令的输出，但在这之前，你可以查看它们，并实验自己的一些  ``#check`` 命令。

让我们尝试一些更多的示例。定理 ``two_mul a`` 表明 ``2 * a = a + a``. 
定理 ``add_mul`` 和 ``mul_add`` 表达了乘法对加法的分配性质，而定理 ``add_assoc`` 表达了加法的结合性。使用 ``#check`` 命令查看准确的表述。

.. index:: calc, tactics ; calc
TEXT. -/
section
variable (a b : ℝ)

-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]
-- QUOTE.

/- TEXT:
虽然可以通过在编辑器中逐步查看来弄清楚这个证明的内容，但它本身很难读懂。
Lean 提供了一种更结构化的方式来编写类似这样的证明，使用 ``calc`` 关键字。
TEXT. -/
-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]
-- QUOTE.

/- TEXT:
请注意，证明 *不* 以 ``by`` 开头：以 ``calc`` 开头的表达式是一个 *证明项*。 ``calc`` 表达式也可以在策略证明中使用，
但 Lean 把它解释为使用结果证明项来解决目标的指令。 ``calc`` 语法很挑剔：下划线和论证必须按照上面指示的格式。
Lean 使用缩进来确定诸如策略块或 ``calc`` 块的起始和结束位置；尝试更改上面证明中的缩进以观察会发生什么。

编写 ``calc`` 证明的一种方法是首先用 ``sorry`` 策略对其进行概述，确保 Lean 接受这些表达式，然后使用策略来证明每个步骤。
TEXT. -/
-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry
-- QUOTE.

end

/- TEXT:
尝试分别使用纯 ``rw`` 证明和更结构化的 ``calc`` 证明来证明以下恒等式：
TEXT. -/
-- Try these. For the second, use the theorems listed underneath.
section
variable (a b c d : ℝ)

-- QUOTE:
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry
-- QUOTE.

/- TEXT:
以下练习稍微有点挑战性。你可以使用下面列出的定理。
TEXT. -/
-- QUOTE:
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
-- QUOTE.

end

/- TEXT:
.. index:: rw, tactics ; rw and rewrite

我们还可以在上下文的假设中进行重写。例如， ``rw [mul_comm a b] at hyp`` 将在假设 ``hyp`` 中将 ``a * b`` 替换为 ``b * a``. 
TEXT. -/
-- Examples.

section
variable (a b c d : ℝ)

-- QUOTE:
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp
-- QUOTE.

/- TEXT:
.. index:: exact, tactics ; exact

在最后一步中， ``exact`` 策略可以使用 ``hyp`` 来解决目标，因为在那个位置， ``hyp`` 精确地匹配了目标。

.. index:: ring (tactic), tactics ; ring

在本节最后，我们将看到，Mathlib 提供了一个有用的自动化工具，即 ``ring`` 策略，它旨在证明在任何交换环中的恒等式，
只要这些恒等式纯粹是由环的公理推导出来的，而没有使用任何局部假设。
TEXT. -/
-- QUOTE:
example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
-- QUOTE.

end

/- TEXT:
``ring`` 策略是在我们导入 ``Mathlib.Data.Real.Basic`` 的时候间接导入的，但我们将在下一节中看到它可以用于除了实数之外的其他结构的计算。
可以使用命令 ``import Mathlib.Tactic`` 明确导入它。我们将会看到，有一些类似的策略适用于其他常见类型的代数结构。

还有一个名为 ``nth_rw`` 的 ``rw`` 的变体，它允许你仅替换目标中特定的表达式实例。
可能的匹配项从 1 开始枚举，所以在下面的例子中， ``nth_rw 2 [h]`` 将用 ``c`` 替换第二个出现的 ``a + b``. 
EXAMPLES: -/
-- QUOTE:
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
-- QUOTE.