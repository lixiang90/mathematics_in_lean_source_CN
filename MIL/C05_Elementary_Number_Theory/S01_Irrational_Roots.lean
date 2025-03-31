import MIL.Common
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
/- OMIT:
-- fix this.
-- import Mathlib.Data.Real.Irrational
BOTH: -/

/- TEXT:
.. _section_irrational_roots:

无理根
----------------

让我们从古希腊人知道的一个事实开始，即 2 的平方根是无理数。
如果我们假定并非如此，
则我们可以将其表示为最简分数 :math:`\sqrt{2} = a / b`.
两边取平方得到 :math:`a^2 = 2 b^2`,
这意味着 :math:`a` 是偶数。
如果我们记 :math:`a = 2c`, 则有 :math:`4c^2 = 2 b^2`,
从而 :math:`b^2 = 2 c^2`.
这意味着 :math:`b` 也是偶数，
这和我们假设的事实，即 :math:`a / b` 已约分到最简矛盾。

称 :math:`a / b` 是最简分数意味着 :math:`a` 和 :math:`b` 没有任何公因子，
也就是说，它们是 *互素* 的。
Mathlib 把谓词 ``Nat.Coprime m n`` 定义为 ``Nat.gcd m n = 1``.
使用 Lean 的匿名投影记号，如果 ``s`` 和 ``t`` 是 ``Nat`` 类型的表达式，
我们可以用 ``s.Coprime t`` 替代 ``Nat.Coprime s t``,
而 ``Nat.gcd`` 也有类似的表达方式。
像往常一样，Lean 通常会在必要时自动展开 ``Nat.Coprime`` 的定义，
但我们也可以通过重写或简化标识符 ``Nat.Coprime`` 来手动操作。
``norm_num`` 策略足够智能，可以计算具体值。
EXAMPLES: -/
-- QUOTE:
#print Nat.Coprime

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
  h

example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
  rw [Nat.Coprime] at h
  exact h

example : Nat.Coprime 12 7 := by norm_num

example : Nat.gcd 12 8 = 4 := by norm_num
-- QUOTE.

/- TEXT:
我们已经在 :numref:`more_on_order_and_divisibility` 中遇到过 ``gcd`` 函数。
还有一个用于整数的 ``gcd`` 版本；
我们将在下面回到不同数系之间关系的讨论中。
甚至还有广义 ``gcd`` 函数以及广义 ``Prime`` 和 ``Coprime`` 的概念，
它们在一般类型的代数结构中有意义。
我们将在下一章了解 Lean 是如何管理这种一般性的。
同时，在本节中，我们将把注意力限制到自然数。

我们还需要素数的概念， ``Nat.Prime``.
定理 ``Nat.prime_def_lt`` 提供了一个熟悉的刻画，
``Nat.Prime.eq_one_or_self_of_dvd`` 提供了另一个。
EXAMPLES: -/
-- QUOTE:
#check Nat.prime_def_lt

example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
  rwa [Nat.prime_def_lt] at prime_p

#check Nat.Prime.eq_one_or_self_of_dvd

example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
  prime_p.eq_one_or_self_of_dvd

example : Nat.Prime 17 := by norm_num

-- commonly used
example : Nat.Prime 2 :=
  Nat.prime_two

example : Nat.Prime 3 :=
  Nat.prime_three
-- QUOTE.

/- TEXT:
在自然数中，素数具有不能写成非平凡因子的乘积的性质。
在更广泛的数学背景下，环中具有此性质的元素被称为 *不可约* 的。
环的元素称为 *素元*，如果每当它整除一个乘积时，它整除其中一个因子。
自然数的一个重要性质是，对它来说这两个概念是一致的，
这产生了定理 ``Nat.Prime.dvd_mul``.

我们可以利用这个事实建立上面论证中的一个关键性质：
如果一个数的平方是偶数，那么这个数也是偶数。
Mathlib 在 ``Algebra.Group.Even`` 中定义了谓词 ``Even``,
但出于下面会澄清的原因，
我们将简单地用 ``2 ∣ m`` 表示 ``m`` 是偶数。
EXAMPLES: -/
-- QUOTE:
#check Nat.Prime.dvd_mul
#check Nat.Prime.dvd_mul Nat.prime_two
#check Nat.prime_two.dvd_mul

-- BOTH:
theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
  rw [pow_two, Nat.prime_two.dvd_mul] at h
  cases h <;> assumption

-- EXAMPLES:
example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
-- QUOTE.

/- TEXT:
随着我们的继续，你将需要熟练地查找所需的事实。
请记住，如果你能猜出名称的前缀并且你已经导入了相关库，
你可以使用制表符补全（有时使用 ``ctrl-tab``）来查找你在寻找的东西。
你可以在任何标识符上使用 ``ctrl-click`` 来跳转到文件中它的定义所在位置，
使你能够浏览附近的定义和定理。
你也可以使用
`Lean community web pages <https://leanprover-community.github.io/>`_
里的搜索引擎，
如果其他方法都失败了，
不要羞于向
`Zulip <https://leanprover.zulipchat.com/>`_
提问。
EXAMPLES: -/
-- QUOTE:
example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
  -- apply? suggests the following:
  (mul_right_inj' h').mp h
-- QUOTE.

/- TEXT:
我们对根号二无理性证明的核心包含在下列定理中。
看看你能不能填补这个证明梗概，
请使用 ``even_of_even_sqr`` 以及定理 ``Nat.dvd_gcd``.
BOTH: -/
-- QUOTE:
example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
  intro sqr_eq
  have : 2 ∣ m := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply even_of_even_sqr
    rw [sqr_eq]
    apply dvd_mul_right
-- BOTH:
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : 2 * k ^ 2 = n ^ 2 :=
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    (mul_right_inj' (by norm_num)).mp this
-- BOTH:
  have : 2 ∣ n := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply even_of_even_sqr
    rw [← this]
    apply dvd_mul_right
-- BOTH:
  have : 2 ∣ m.gcd n := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.dvd_gcd <;>
    assumption
-- BOTH:
  have : 2 ∣ 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    convert this
    symm
    exact coprime_mn
-- BOTH:
  norm_num at this
-- QUOTE.

/- TEXT:
事实上，只需很少的改变，我们就可以把 ``2`` 替换为任意素数。
在下一个例子中试一试。
在证明的末尾，你需要由 ``p ∣ 1`` 导出矛盾。
你可以使用 ``Nat.Prime.two_le``,
它是说任意素数大于或等于二，
以及 ``Nat.le_of_dvd``.
BOTH: -/
-- QUOTE:
example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  intro sqr_eq
  have : p ∣ m := by
    apply prime_p.dvd_of_dvd_pow
    rw [sqr_eq]
    apply dvd_mul_right
  obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
  have : p * (p * k ^ 2) = p * n ^ 2 := by
    rw [← sqr_eq, meq]
    ring
  have : p * k ^ 2 = n ^ 2 := by
    apply (mul_right_inj' _).mp this
    exact prime_p.ne_zero
  have : p ∣ n := by
    apply prime_p.dvd_of_dvd_pow
    rw [← this]
    apply dvd_mul_right
  have : p ∣ Nat.gcd m n := by apply Nat.dvd_gcd <;> assumption
  have : p ∣ 1 := by
    convert this
    symm
    exact coprime_mn
  have : 2 ≤ 1 := by
    apply prime_p.two_le.trans
    exact Nat.le_of_dvd zero_lt_one this
  norm_num at this
-- QUOTE.

-- BOTH:
/- TEXT:
我们考虑另一种思路。
这是若 :math:`p` 是素数则 :math:`m^2 \ne p n^2` 的一个快速证明：
如果我们假设 :math:`m^2 = p n^2`,
考虑 :math:`m` 和 :math:`n` 的素分解，
则 :math:`p` 在等式左边出现偶数次而在右边出现奇数次，矛盾。
注意到这个论证要求 :math:`n`, 从而 :math:`m`,
不等于零。
下面的形式化证实了这个假设是充分的。

唯一因子分解定理表明，
任何大于零的自然数可以用唯一的方式写成素数的乘积。
Mathlib 包含其形式化版本，使用函数 ``Nat.primeFactorsList`` 表达，
该函数以非递减顺序返回数的素因数列表。
此库证明了 ``Nat.factors n`` 的全部元素都是素数，
任意大于零的 ``n`` 等于它的因子的乘积，
以及若 ``n`` 等于另一列素数的乘积，
则这个列是 ``Nat.factors n`` 的一个排列。
EXAMPLES: -/
-- QUOTE:
#check Nat.primeFactorsList
#check Nat.prime_of_mem_primeFactorsList
#check Nat.prod_primeFactorsList
#check Nat.primeFactorsList_unique
-- QUOTE.

/- TEXT:
你可以浏览这些定理和附近的其他定理，
即使我们还没有谈到列表成员、乘积或排列。
我们手头的任务不需要这些。
我们会使用 Mathlib 函数 ``Nat.factorization`` 作为替代品，
它把同样的数据表示为函数。
特别地，``Nat.factorization n p``,
也记为 ``n.factorization p``,
返回 ``n`` 的素分解中 ``p`` 的重数。
我们将用到以下三个事实。
BOTH: -/
-- QUOTE:
theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
    (m * n).factorization p = m.factorization p + n.factorization p := by
  rw [Nat.factorization_mul mnez nnez]
  rfl

theorem factorization_pow' (n k p : ℕ) :
    (n ^ k).factorization p = k * n.factorization p := by
  rw [Nat.factorization_pow]
  rfl

theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
    p.factorization p = 1 := by
  rw [prime_p.factorization]
  simp
-- QUOTE.

/- TEXT:
事实上，``n.factorization`` 在 Lean 中被定义为有限支集的函数，
这解释了你在逐步查看上述证明时会看到的奇怪符号。
现在不用担心这个。
出于我们这里的目的，我们可以将上面三个定理作为黑盒使用。

下一个示例表明化简器足够智能，
可以把 ``n^2 ≠ 0`` 替换为 ``n ≠ 0``.
策略 ``simpa`` 不过是先调用 ``simp`` 接下来用 ``assumption``.

看看你是否可以用上面的等式来填补证明缺失的部分。
BOTH: -/
-- QUOTE:
example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
  intro sqr_eq
  have nsqr_nez : n ^ 2 ≠ 0 := by simpa
  have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [factorization_pow']
-- BOTH:
  have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [factorization_mul' prime_p.ne_zero nsqr_nez, prime_p.factorization', factorization_pow',
      add_comm]
-- BOTH:
  have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
    rw [← eq1, sqr_eq, eq2]
  rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
  norm_num at this
-- QUOTE.

/- TEXT:
这个证明的一个好处是它的可推广性。
``2`` 没什么特别的；通过少量修改，
证明指出只要我们有 ``m^k = r * n^k``,
``r`` 中素数 ``p`` 的重数就只能是 ``k`` 的倍数。

为了对 ``r * n^k`` 使用 ``Nat.count_factors_mul_of_pos``,
我们需要知道 ``r`` 是正的。
但当 ``r`` 是零时，下面的定理是平凡的，
可使用化简器轻易证明。
所以证明是分情况进行的。
``rcases r with _ | r`` 这一行把目标替换为两个版本：
一个把 ``r`` 替换为 ``0``,
另一个把 ``r`` 替换为 ``r`` 的后继 ``r.succ``.
在第二种情况下，我们可以应用定理 ``r.succ_ne_zero``,
由它可得 ``r + 1 ≠ 0`` （ ``succ`` 表示后继）

另请注意，以 ``have : npow_nz`` 开头的行提供了 ``n^k ≠ 0`` 的简短证明项证明。
要理解它是如何工作的，请尝试用策略证明替换它，
然后思考策略如何描述证明项。

看看你是否可以填补下列证明中缺失的部分。
在最后，你可以使用 ``Nat.dvd_sub'`` 和 ``Nat.dvd_mul_right`` 来收尾。
BOTH: -/
-- QUOTE:
example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
    k ∣ r.factorization p := by
  rcases r with _ | r
  · simp
  have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
  have eq1 : (m ^ k).factorization p = k * m.factorization p := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [factorization_pow']
-- BOTH:
  have eq2 : ((r + 1) * n ^ k).factorization p =
      k * n.factorization p + (r + 1).factorization p := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [factorization_mul' r.succ_ne_zero npow_nz, factorization_pow', add_comm]
-- BOTH:
  have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
    rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
  rw [this]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  apply Nat.dvd_sub' <;>
  apply Nat.dvd_mul_right
-- BOTH:
-- QUOTE.

/- TEXT:
我们可能希望通过多种方式来改进这些结果。
首先，根号二是无理数的证明应该涉及一些和根号二相关的结论，
称它是无理数应该提到一些关于有理数的事情，即没有有理数等于它。
此外，我们应该将本节中的定理扩展到整数。
虽然数学上显而易见的是，如果我们可以将二的平方根写为两个整数的商，
那么我们就可以将其写为两个自然数的商，
但形式上证明这一点需要一些努力。

在 Mathlib 中，自然数、整数、有理数、实数和复数用不同的数据类型表示。
把注意力限制在单独的领域中常常是有帮助的：
我们将看到在自然数上做归纳法容易，
涉及整数的整除性的推理也很容易，
但实数就不在这些图景中。
但必须在不同领域中进行协调是我们将不得不面对的一个令人头疼的问题。
我们将在本章后面回到这个问题。

我们还应该期望能把上一个定理的结论加强为数 ``r`` 是 ``k`` 次幂，
因为它的 ``k`` 次根恰好是每个整除 ``r`` 的素数以
``r`` 除以 ``k`` 的重数为幂次的幂的乘积。
为了能够做到这一点，
我们需要更好的方法来做关于有限集合上的乘积与和的推理，
这也是我们将要回到的话题。

事实上，本节中的结果都已经在 Mathlib 的
``Data.Real.Irrational`` 中以远为广义的方式建立。
``multiplicity`` 的概念在任意的交换幺半环上定义，
它的取值在扩展自然数 ``enat`` 中，
即在自然数中添加无穷值。
在下一章中，
我们将开始发展一些方法从而理解 Lean 支持这类一般性的途径。
EXAMPLES: -/
#check multiplicity

-- OMIT: TODO: add when available
-- #check irrational_nrt_of_n_not_dvd_multiplicity

-- #check irrational_sqrt_two

-- OMIT:
-- TODO: use this in the later section and then delete here.
#check Rat.num
#check Rat.den

section
variable (r : ℚ)

#check r.num
#check r.den
#check r.pos
#check r.reduced

end

-- example (r : ℚ) : r ^ 2 ≠ 2 := by
--   rw [← r.num_div_denom, div_pow]
--   have : (r.denom : ℚ) ^ 2 > 0 := by
--     norm_cast
--     apply pow_pos r.pos
--   have := Ne.symm (ne_of_lt this)
--   intro h
--   field_simp [this]  at h
--   norm_cast at h
--   sorry
