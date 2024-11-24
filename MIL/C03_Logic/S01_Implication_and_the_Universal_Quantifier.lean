-- BOTH:
import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S01

/- TEXT:
.. _implication_and_the_universal_quantifier:

蕴含和全称量词
----------------------------------------

请看 ``#check`` 后面的语句：
TEXT. -/
-- QUOTE:
#check ∀ x : ℝ, 0 ≤ x → |x| = x
-- QUOTE.

/- TEXT:
自然语言表述为 "对于每个实数 ``x``, 若 ``0 ≤ x``, 则 
``x`` 的绝对值等于 ``x``".
我们还可以有更复杂的语句，例如：
TEXT. -/
-- QUOTE:
#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε
-- QUOTE.

/- TEXT:
自然语言表述为 "对于任意的 ``x``, ``y``, 以及 ``ε``,
若 ``0 < ε ≤ 1``, ``x`` 的绝对值小于 ``ε``, 
且 ``y`` 的绝对值小于 ``ε``,
则 ``x * y`` 的绝对值小于 ``ε``."
在Lean中，一连串的蕴含中有隐含的右结合括号。
所以上述表达式的意思是
"若 ``0 < ε``, 则若 ``ε ≤ 1``, 则若 ``|x| < ε`` ..."
因此，表达式表示所有假设组合在一起导出结论。

你已经看到，
尽管这个语句中全称量词的取值范围是对象，
而蕴涵箭头引入的是假设，
但Lean处理这两者的方式非常相似。
特别地，如果你已经证明了这种形式的定理，
你就可以用同样的方法把它应用于对象和假设。
我们将以下面的语句为例，稍后我们会帮你证明它：
TEXT. -/
-- QUOTE:
theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end
-- QUOTE.

/- TEXT:
你也已经看到，在Lean中，当量化变量可以从后面的假设中推断出来时，
使用大括号将其隐去是很常见的。
当我们这样做的时候，
我们就可以直接将引理应用到假设中，
而无需提及对象。
TEXT. -/
-- QUOTE:
theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end
-- QUOTE.

/- TEXT:
在当前阶段，你也知道如果你使用 ``apply`` 
策略将 ``my_lemma`` 应用于形如 ``|a * b| < δ`` 的目标，
就会留下一些新的目标，它们要求你证明引理的每个假设。

.. index:: intro, tactics; intro

要证明与此类似的语句，需使用 ``intro`` 策略。
在这个例子中观察一下该策略做了什么：
TEXT. -/
-- QUOTE:
theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  sorry
-- QUOTE.

/- TEXT:
我们可以对全称量化变量使用任何我们想用的名字；
并非一定要是 ``x``, ``y`` 和 ``ε``.
注意我们必须引入变量，即使它们被标记为隐式的：
让它们隐去的意思是当我们 *使用* ``my_lemma`` 写一个表达式时不写它们，
但它们仍然是我们要证明的语句的重要组成部分。
在 ``intro`` 命令之后，
如果我们在冒号 *之前* 列出所有变量和假设，目标就会和开始时一样，
就像我们在上一节中做的那样。
稍后，我们将看到为什么有时候有必要在证明开始之后引入变量和假设。

为了帮你证明这个引理，我们会给你开个头：
TEXT. -/
-- QUOTE:
-- BOTH:
theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
/- EXAMPLES:
  calc
    |x * y| = |x| * |y| := sorry
    _ ≤ |x| * ε := sorry
    _ < 1 * ε := sorry
    _ = ε := sorry

SOLUTIONS: -/
  calc
    |x * y| = |x| * |y| := by apply abs_mul
    _ ≤ |x| * ε := by apply mul_le_mul; linarith; linarith; apply abs_nonneg; apply abs_nonneg;
    _ < 1 * ε := by rw [mul_lt_mul_right epos]; linarith
    _ = ε := by apply one_mul
-- QUOTE.

/- TEXT:
使用定理 ``abs_mul``, ``mul_le_mul``, ``abs_nonneg``,
``mul_lt_mul_right`` 和 ``one_mul`` 完成证明。
记住你可以使用Ctrl-space补全（或者，在Mac中，Cmd-space补全）找到像这样的定理。
也记住你可以使用 ``.mp`` 和 ``.mpr``
或者 ``.1`` 和 ``.2`` 来提取一个当且仅当语句的两个方向。

全称量词通常隐藏在定义中，
Lean 会在必要时展开定义以暴露它们。
例如，让我们定义两个谓词，
``FnUb f a`` 和 ``FnLb f a``,
其中 ``f`` 是一个从实数到实数的函数，
而 ``a`` 是一个实数。
第一个谓词是说 ``a`` 是 ``f`` 的值的一个上界，
而第二个是说 ``a`` 是 ``f`` 的值的一个下界。
BOTH: -/
-- QUOTE:
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x
-- QUOTE.

/- TEXT:
.. index:: lambda abstraction

在下一个例子中， ``fun x ↦ f x + g x`` 是把 ``x`` 映射到 `` f x + g x`` 的函数。
从表达式 ``f x + g x`` 到这个函数，
在类型论中称为lambda抽象。
BOTH: -/
section
variable (f g : ℝ → ℝ) (a b : ℝ)

-- EXAMPLES:
-- QUOTE:
example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb
-- QUOTE.

/- TEXT:
.. index:: dsimp, tactics ; dsimp, change, tactics ; change

把 ``intro`` 应用于目标 ``FnUb (fun x ↦ f x + g x) (a + b)`` 
迫使 Lean 展开 ``FnUb`` 的定义并引入 ``x`` 作为全称量词。
此时目标为 ``(fun (x : ℝ) ↦ f x + g x) x ≤ a + b``.
但在 ``(fun x ↦ f x + g x)`` 上取值 ``x`` 的结果应该是 ``f x + g x``,
而 ``dsimp`` 命令执行了这个简化。
（其中 "d" 是指 "定义性的"）
你可以删除这个命令，证明仍然有效；
Lean将不得不执行那个化简，才能使下一个 ``apply`` 有意义。
``dsimp`` 命令只是让目标更可读，并帮我们弄清楚下一步要做什么。
另一种选择是通过输入 ``change f x + g x ≤ a + b`` 
来使用 ``change`` 策略。 
这有助于提高证明的可读性，
并让你对目标的转换方式有更多的控制。

证明的其余部分都是例行公事。
最后两条 ``apply`` 命令迫使 Lean 展开假设中 ``FnUb`` 的定义。
请尝试进行类似的证明：
TEXT. -/
-- QUOTE:
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) :=
  sorry

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 :=
  sorry

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  intro x
  apply add_le_add
  apply hfa
  apply hgb

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  intro x
  apply mul_nonneg
  apply nnf
  apply nng

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  intro x
  apply mul_le_mul
  apply hfa
  apply hgb
  apply nng
  apply nna

-- BOTH:
end

/- TEXT:
虽然我们已对从实数到实数的函数定义了 ``FnUb`` 和 ``FnLb``,
你应该认识到，这些定义和证明远比这更一般。
这定义对任何两个类型之间的函数有意义，只要值域上有序的概念。
检查定理 ``add_le_add`` 的类型，
发现它对任何是"有序加法交换幺半群"的结构成立；
这个名词的详细含义目前无关紧要，
但值得注意的是自然数、整数、有理数和实数都属于这种情况。
因此，如果我们在如此的广义水平上证明了定理 ``fnUb_add``,
那么它将可用于所有这些实例中。
TEXT. -/
section
-- QUOTE:
variable {α : Type*} {R : Type*} [OrderedCancelAddCommMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)
-- QUOTE.

end

/- TEXT:
你在
Section :numref:`proving_identities_in_algebraic_structures` 中已经看到过像这样的方括号，
但我们仍未解释它们是什么含义。
为了具体性，在我们的大多数例子中，我们专注于实数，
但值得注意的是，Mathlib包含一些具有很高通用性的定义和定理。

.. index:: monotone function

再举一个隐藏全称量词的例子， 
Mathlib 定义了一个谓词 ``Monotone``,
表示函数相对于参数是非递减的：
TEXT. -/
-- QUOTE:
example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h
-- QUOTE.

/- TEXT:
性质 ``Monotone f`` 的定义和冒号后的表达式精确相同。
我们需要在 ``h`` 之前输入 ``@`` 符号，
因为如果我们不这样做，
Lean 会展开 ``h`` 的隐含参数并插入占位符。

证明有关单调性的语句需要使用 ``intro`` 引入两个变量，例如 ``a`` 和 ``b``, 以及假设 ``a ≤ b``.
要使用单调性假设，可以将其应用于合适的参数和假设，然后将得到的表达式应用于目标。
或者，你也可以将它应用到目标上，然后让 Lean 通过将剩余的假设显示为新的子目标来帮助你向后工作。
BOTH: -/
section
variable (f g : ℝ → ℝ)

-- EXAMPLES:
-- QUOTE:
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb
-- QUOTE.

/- TEXT:
当一个证明如此简短时，给出一个证明项往往更方便。
描述一个临时引入对象 
``a`` 和 ``b`` 以及假设 ``aleb`` 的证明时，
Lean 使用符号 ``fun a b aleb ↦ ...``.
这类似于用 ``fun x ↦ x^2`` 这样的表达式来描述一个函数时，
先暂时命名一个对象 ``x``, 然后用它来描述函数的值。
因此，上一个证明中的 ``intro`` 命令
对应于下一个证明项中的 lambda 抽象。
``apply`` 命令则对应于构建定理对其参数的应用。
TEXT. -/
-- QUOTE:
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)
-- QUOTE.

/- TEXT:
这里有一个有用的小窍门：如果在开始编写证明项 ``fun a b aleb ↦ _`` 时，
在表达式的其余部分使用下划线，
Lean 就会提示错误，表明它无法猜测该表达式的值。
如果你检查VS Code中的 Lean 目标窗口或把鼠标悬停在标着波浪线的错误标识符上，
Lean 会向你显示剩余的表达式需要解决的目标。

尝试证明它们，可以使用策略或证明项：
TEXT. -/
-- QUOTE:
example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  sorry

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  intro a b aleb
  apply mul_le_mul_of_nonneg_left _ nnc
  apply mf aleb

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  fun a b aleb ↦ mul_le_mul_of_nonneg_left (mf aleb) nnc

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  intro a b aleb
  apply mf
  apply mg
  apply aleb

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  fun a b aleb ↦ mf (mg aleb)

/- TEXT:
这里是另一些例子。
一个从 :math:`\Bbb R` 到 :math:`\Bbb R` 的函数 :math:`f` 
称为 *偶函数*，如果对每个 :math:`x`, 有 :math:`f(-x) = f(x)`, 
称为 *奇函数*，如果对每个 :math:`x`, 有 :math:`f(-x) = -f(x)`. 
下面的例子形式化地定义了这两个概念，并确立了关于它们的一个事实。
你可以完成其他事实的证明。
TEXT. -/
-- QUOTE:
-- BOTH:
def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

-- EXAMPLES:
example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  intro x
  calc
    (fun x ↦ f x * g x) x = f x * g x := rfl
    _ = f (-x) * g (-x) := by rw [of, og, neg_mul_neg]


example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  intro x
  dsimp
  rw [ef, og, neg_mul_eq_mul_neg]

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  intro x
  dsimp
  rw [og, ← ef]

-- BOTH:
end

/- TEXT:
.. index:: erw, tactics ; erw

通过使用 ``dsimp`` 或 ``change`` 消除lambda抽象，
可以缩短第一个证明。
但你可以验证，除非我们准确地消除lambda抽象，否则接下来的 ``rw`` 不会生效，
因为此时它无法在表达式中找到样式 ``f x`` 和 ``g x``.
和其他一些策略不同， ``rw`` 作用于语法层次，
它不会为你展开定义或应用还原（它有一个变种称为 ``erw``, 在这个方向上会努力一点，但也不会努力太多）。

到处都能找到隐式全称量词，
只要你知道如何发现它们。

Mathlib 包含一个用于操作集合的优秀的库。回想一下，Lean 并不使用基于集合论的基础，因此在这里，集合一词具有普通含义，即某个给定类型 ``α`` 的数学对象的汇集。
如果 ``x`` 具有类型 ``α``, 而 ``s`` 具有类型 ``Set α``, 则 ``x ∈ s`` 是一个命题，
它断言 ``x`` 是 ``s`` 的一个元素。若 ``y`` 具有另一个类型 ``β`` 则表达式 ``y ∈ s`` 无意义。这里 "无意义" 的含义是 "没有类型因此 Lean 不认可它是一个良好形式的语句"。
这与 Zermelo-Fraenkel 集合论不同，
例如其中对于每个数学对象 ``a`` 和 ``b``, ``a∈b`` 都是良好形式的语句。
例如， ``sin ∈ cos`` 是 ZF 中一个格式良好的语句。
集合论基础的这一缺陷是证明助手中不使用它的一个重要原因，因为证明助手的目的是帮助我们检出无意义的表达式。在 Lean 中， ``sin`` 具有类型 ``ℝ → ℝ``, 而 ``cos`` 具有类型 ``ℝ → ℝ``, 
它不等于 ``Set (ℝ → ℝ)``, 即使在展开定义以后也不相等，因此语句 ``sin ∈ cos`` 无意义。
我们还可以利用 Lean 来研究集合论本身。
例如，连续统假设与 Zermelo-Fraenkel 公理的独立性就在 Lean 中得到了形式化。
但这种集合论的元理论完全超出了本书的范围。

若 ``s`` 和 ``t`` 具有类型 ``Set α``,
那么子集关系 ``s ⊆ t`` 被定义为
``∀ {x : α}, x ∈ s → x ∈ t``.
量词中的变量被标记为隐式，
因此给出 ``h : s ⊆ t`` 和 ``h' : x ∈ s``,
我们可以把 ``h h'`` 作为 ``x ∈ t`` 的证明。
下面的例子提供了一个策略证明和一个证明项，
证明了子集关系的反身性，
并要求你对传递性做同样的证明。
TEXT. -/
-- BOTH:
section

-- QUOTE:
variable {α : Type*} (r s t : Set α)

-- EXAMPLES:
example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : r ⊆ s → s ⊆ t → r ⊆ t := by
  intro rsubs ssubt x xr
  apply ssubt
  apply rsubs
  apply xr

theorem Subset.transαα : r ⊆ s → s ⊆ t → r ⊆ t :=
  fun rsubs ssubt x xr ↦ ssubt (rsubs xr)

-- BOTH:
end

/- TEXT:
就像我们对函数定义了 ``FnUb`` 一样，
假设 ``s`` 是一个由某类型的元素组成的集合，且它具有一个与之关联的序。
我们可以定义 ``SetUb s a``, 意为 ``a`` 是集合 ``s`` 的一个上界。
在下一个例子中，我们要求你证明，
如果 ``a`` 是 ``s`` 的一个上界，且 ``a ≤ b``,
则 ``b`` 也是 ``s`` 的一个上界。
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

-- EXAMPLES:
example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : SetUb s a) (h' : a ≤ b) : SetUb s b := by
  intro x xs
  apply le_trans (h x xs) h'

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  fun x xs ↦ le_trans (h x xs) h'

-- BOTH:
end

/- TEXT:
.. index:: injective function

最后，我们以一个重要的例子来结束本节。
函数 :math:`f` 称为 *单射*, 若对每个 :math:`x_1` 和 :math:`x_2`,
如果 :math:`f(x_1) = f(x_2)`, 那么 :math:`x_1 = x_2`.
Mathlib定义了 ``Function.Injective f``, 其中 ``x₁`` 和 ``x₂`` 是隐含的。
下一个例子表明，在实数上，任何由自变量加上非零常数得到的函数都是单射。
然后，我们要求您利用示例中的引理名称作为灵感来源，
证明非零常数乘法也是单射的。
请记住，在猜出一个引理名称的开头后，应使用 Ctrl-space 补全。
TEXT. -/
-- BOTH:
section

-- QUOTE:
open Function

-- EXAMPLES:
example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  intro x₁ x₂ h'
  apply (mul_right_inj' h).mp h'

/- TEXT:
最后，证明两个单射函数的复合是单射：
BOTH: -/
-- QUOTE:
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

-- EXAMPLES:
example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  intro x₁ x₂ h
  apply injf
  apply injg
  apply h

-- BOTH:
end
