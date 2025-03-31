import Mathlib.Data.Nat.Prime.Basic
import MIL.Common

open BigOperators

namespace C05S03

/- TEXT:
.. _section_infinitely_many_primes:

素数无穷
----------------------

让我们用另一个标准数学定理继续探索归纳和递归：证明素数有无穷多个。
一种表述方式是，对于每个自然数 :math:`n`,
都有一个大于 :math:`n` 的素数。
为了证明这一点，令 :math:`p` 是 :math:`n! + 1` 的任意一个素因子。
若 :math:`p` 小于等于 :math:`n`, 则它整除 :math:`n!`.
由于它也整除 :math:`n! + 1`, 它整除 1, 矛盾。
因此，:math:`p` 大于 :math:`n`.

为了形式化这个证明，
我们需要论证任何大于或等于 2 的数都有一个素因数。
为此，我们需要证明任何不等于 0 或 1 的自然数都大于或等于 2.
这就给我们带来了形式化的一个古怪特征：
像这样琐碎的语句往往是最难形式化的。
在此，我们考虑几种方法。

首先，我们可以使用 ``cases`` 策略，
以及后继函数尊重自然数顺序这一事实。
BOTH: -/
-- QUOTE:
theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat apply Nat.succ_le_succ
    apply zero_le
-- QUOTE.

/- TEXT:
另一种方式是使用策略 ``interval_cases``,
当相关变量包含在自然数或整数的区间内时，
它会自动将目标分割成不同的情况。
请记住，你可以将鼠标悬停在该策略上以查看其文档。
EXAMPLES: -/
-- QUOTE:
example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  interval_cases m <;> contradiction
-- QUOTE.

/- TEXT:
.. index:: decide, tactics ; decide

回想一下，``interval_cases m``
后面的分号表示下一个策略将应用于它生成的每种情况。
还有一种方法是使用 ``decide`` 策略，
该策略尝试找到一个决策过程来解决问题。
Lean 知道可以通过对有限个实例逐一进行判定，
来确定一个以有界量词
``∀ x, x < n → ...`` 或 ``∃ x, x < n ∧ ...`` 开头的语句的真值。
EXAMPLES: -/
-- QUOTE:
example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  by_contra h
  push_neg at h
  revert h0 h1
  revert h m
  decide
-- QUOTE.

/- TEXT:
手中有了 ``two_le`` 这个定理，
我们就可以从证明每个大于 2 的自然数都有一个素数除数开始。
Mathlib 包含一个函数 ``Nat.minFac``,
它能返回最小的素数除数，但为了学习库的新部分，
我们将避免使用它，而是直接证明定理。

在这里，常规的归纳法是不够的。
我们需要用 *强归纳法*，
它允许我们通过证明对每个数 :math:`n`,
若性质 :math:`P` 对所有小于 :math:`n` 的值都成立，
则对 :math:`n` 也成立，
来证明每个自然数 :math:`n` 都有性质 :math:`P`.
在 Lean 中，这个原则被称为 ``Nat.strong_induction_on``,
我们可以使用 ``using`` 关键字告诉归纳策略去使用它。
请注意，当我们这样做时，就没有归纳奠基了；
它已被一般归纳步骤所包含。

论证简述如下。假设 :math:`n≥2`,
如果 :math:`n` 是素数，我们的证明就完成了。
如果不是，那么根据何为素数的刻画之一，
它有一个非平凡因子 :math:`m`,
我们就可以对其应用归纳假设。
分步查看下一个证明以观察其推理过程是如何完成的。
BOTH: -/
-- QUOTE:
theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn
-- QUOTE.

/- TEXT:
我们现在可以证明我们定理的下列表述形式。
看看你能否填补这个梗概。
你可以使用 ``Nat.factorial_pos``, ``Nat.dvd_factorial``,
以及 ``Nat.dvd_sub``.
BOTH: -/
-- QUOTE:
theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
  intro n
  have : 2 ≤ Nat.factorial n + 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.succ_le_succ
    exact Nat.succ_le_of_lt (Nat.factorial_pos _)
-- BOTH:
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  refine ⟨p, ?_, pp⟩
  show p > n
  by_contra ple
  push_neg at ple
  have : p ∣ Nat.factorial n := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.dvd_factorial
    apply pp.pos
    linarith
-- BOTH:
  have : p ∣ 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    convert Nat.dvd_sub' pdvd this
    simp
-- BOTH:
  show False
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have := Nat.le_of_dvd zero_lt_one this
  linarith [pp.two_le]

-- BOTH:
-- QUOTE.
/- TEXT:
让我们考虑上述证明的一种变式，
其中为了代替阶乘函数，
我们假设给定了一个有限集 :math:`\{ p_1, \ldots, p_n \}`,
考虑 :math:`\prod_{i = 1}^n p_i + 1` 的一个素因子。
素因子必须不同于各个 :math:`p_i`,
这表明不存在包含全部素数的有限集。

形式化这一论证要求我们对有限集进行推理。
在 Lean 中，对于任意类型 ``α``, 类型 ``Finset α``
表示类型为 ``α`` 的元素的有限集。
要对有限集进行计算性推理，就要有一个流程来测试 ``α`` 中的相等性，
这就是为什么下面的片段包含了假设 ``[DecidableEq α]``.
对于像 ``ℕ``, ``ℤ`` 和 ``ℚ`` 这样的具体数据类型，假设自动成立。
在对实数进行推理时，为满足假设可以使用经典逻辑而放弃计算解释。

我们使用 ``open Finset`` 命令来为相关定理提供更短的名称。
不像集合的情况，绝大多数关于有限集的等价不是定义性成立的，
所以它们需要使用诸如
``Finset.subset_iff``, ``Finset.mem_union``, ``Finset.mem_inter``,
以及 ``Finset.mem_sdiff`` 这些等价来手动展开。
我们仍然可以使用 ``ext`` 策略，
把证明两个有限集合相等，
还原为证明其中任意一个集合的每个元素都是另一个集合的元素。
BOTH: -/
-- QUOTE:
open Finset

-- EXAMPLES:
section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  rw [subset_iff]
  intro x
  rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
  tauto

example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
  simp [subset_iff]
  intro x
  tauto

example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
  ext x
  simp
  tauto

end
-- QUOTE.

/- TEXT:
我们使用了一个新技巧：``tauto`` 策略
（以及使用经典逻辑的加强版 ``tauto!``）
可以用来免除命题重言式。
看看你能否用这些方法证明下面的两个例子。
BOTH: -/
section
variable {α : Type*} [DecidableEq α] (r s t : Finset α)

-- QUOTE:
example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  rw [mem_inter, mem_union, mem_union, mem_union, mem_inter]
  tauto

example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
  ext x
  simp
  tauto

-- BOTH:
example : (r \ s) \ t = r \ (s ∪ t) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  ext x
  rw [mem_sdiff, mem_sdiff, mem_sdiff, mem_union]
  tauto

example : (r \ s) \ t = r \ (s ∪ t) := by
  ext x
  simp
  tauto
-- QUOTE.
-- BOTH:

end

/- TEXT:
定理 ``Finset.dvd_prod_of_mem``
告诉我们如果 ``n`` 是有限集 ``s`` 的元素，
那么 ``n`` 整除 ``∏ i ∈ s, i``.
EXAMPLES: -/
-- QUOTE:
example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i ∈ s, i :=
  Finset.dvd_prod_of_mem _ h
-- QUOTE.

/- TEXT:
我们也需要知道在 ``n`` 是素数且 ``s``
是素数集的情况下逆命题成立。
为了说明这一点，我们需要下列引理，
你可以使用定理 ``Nat.Prime.eq_one_or_self_of_dvd`` 证明它。
BOTH: -/
-- QUOTE:
theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
      (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
    p = q := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  cases prime_q.eq_one_or_self_of_dvd _ h
  · linarith [prime_p.two_le]
  assumption
-- QUOTE.
-- BOTH:

/- TEXT:
我们可以使用这个引理证明若素数 ``p`` 整除有限素数集的乘积，
则它整除其中一个素数。
Mathlib 提供了在有限集上做归纳的一个有用法则：
要证明某性质对任意有限集 ``s`` 成立，
先证明其对空集成立，
再证明当添加一个新元素 ``a ∉ s`` 时该性质保持成立。
这个法则被称为 ``Finset.induction_on``.
当我们告诉归纳策略使用它时，
我们还可以指定 ``a`` 和 ``s`` 的名称，
归纳步骤中的假设 ``a ∉ s`` 的名称，以及归纳假设的名称。
表达式 ``Finset.insert a s`` 表示 ``s`` 和单元素集 ``a`` 的并。
然后，等式 ``Finset.prod_empty`` 和 ``Finset.prod_insert``
为乘积提供了相关的重写法则。
在下面的证明中，第一个 ``simp`` 应用了 ``Finset.prod_empty``.
逐步追踪证明的开头，观察归纳的展开，然后完成它。
BOTH: -/
-- QUOTE:
theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
    (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n ∈ s, n) → p ∈ s := by
  intro h₀ h₁
  induction' s using Finset.induction_on with a s ans ih
  · simp at h₁
    linarith [prime_p.two_le]
  simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
  rw [mem_insert]
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rcases h₁ with h₁ | h₁
  · left
    exact prime_p.eq_of_dvd_of_prime h₀.1 h₁
  right
  exact ih h₀.2 h₁

-- BOTH:
-- QUOTE.
/- TEXT:
我们需要最后一个有限集性质。
给定一个元素 ``s : Set α`` 和 ``α`` 上的谓词 ``P``,
在 :numref:`Chapter %s <sets_and_functions>` 中，
我们用 ``{ x ∈ s | P x }`` 表示满足 ``P`` 的元素的集合 ``s``.
给定 ``s : Finset α``,
类似的概念记为 ``s.filter P``.
EXAMPLES: -/
-- QUOTE:
example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
  mem_filter
-- QUOTE.

/- TEXT:
我们现在证明“素数有无穷多个”这一命题的另一种表述，
即给定任意 ``s : Finset ℕ``, 存在一个素数 ``p`` 不是 ``s`` 的元素。
为了导出矛盾，我们假设所有素数都在 ``s`` 中，
然后缩减为一个仅包含所有素数的集合 ``s``.
取该集合的乘积，加一，然后找到结果的一个素因数，
这通向了我们正在寻找的矛盾。
看看你能否完成下面的概要。
你可以在第一个 ``have`` 的证明中使用 ``Finset.prod_pos``.
BOTH: -/
-- QUOTE:
theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i ∈ s', i) + 1 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply Nat.succ_le_succ
    apply Nat.succ_le_of_lt
    apply Finset.prod_pos
    intro n ns'
    apply (mem_s'.mp ns').pos
-- BOTH:
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i ∈ s', i := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply dvd_prod_of_mem
    rw [mem_s']
    apply pp
-- BOTH:
  have : p ∣ 1 := by
    convert Nat.dvd_sub' pdvd this
    simp
  show False
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  have := Nat.le_of_dvd zero_lt_one this
  linarith [pp.two_le]

-- BOTH:
-- QUOTE.
/- TEXT:
由此我们已经见过两种表达“有无穷多个素数”的方式：
说素数不以任何 ``n`` 为上界，和说它们不包含在任何有限集 ``s`` 中。
下面两个证明说明了这些表示方法是等价的。
在第二个证明中，为了构建 ``s.filter Q``, 我们只好假定存在一个能决定 ``Q``
是否成立的过程。Lean知道有一个用于 ``Nat.Prime`` 的过程。一般地，
如果我们键入 ``open Classical`` 以使用经典逻辑，
我们就可以省略这个假设。

在 Mathlib 中， ``Finset.sup s f`` 表示当 ``x`` 取遍 ``s`` 时 ``f x`` 的上确界，
而在 ``s`` 为空且 ``f`` 的到达域为 ``ℕ`` 时返回 ``0``.
在第一个证明中，我们使用 ``s.sup id`` 表示 ``s`` 的最大值，
其中 ``id`` 是恒等函数。
BOTH: -/
-- QUOTE:
theorem bounded_of_ex_finset (Q : ℕ → Prop) :
    (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
  rintro ⟨s, hs⟩
  use s.sup id + 1
  intro k Qk
  apply Nat.lt_succ_of_le
  show id k ≤ s.sup id
  apply le_sup (hs k Qk)

theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
    (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
  rintro ⟨n, hn⟩
  use (range (n + 1)).filter Q
  intro k
  simp [Nat.lt_succ_iff]
  exact hn k
-- QUOTE.

/- TEXT:
我们对存在无穷多个素数的第二个证明做了一个小的改动，
表明有无穷多个模 4 余 3 的素数。
论证如下。
首先，注意到若两个数 :math:`m` 和 :math:`n` 的乘积模 4 等于 3,
那么两个数中有一个模 4 余 3.
毕竟，它们都是奇数，若它们都模 4 余 1,
那么它们的乘积也一样。
我们可以使用这个观察证明若某个大于 2 的数模 4 余 3,
那么那个数有一个模 4 余 3 的素因子。

现在假设只有有限多个素数模 4 余 3,
记为 :math:`p_1, \ldots, p_k`.
不失一般性，我们可以假设 :math:`p_1 = 3`.
考虑乘积 :math:`4 \prod_{i = 2}^k p_i + 3`.
容易看出这个乘积模 4 余 3,
因此它有一个模 4 余 3 的素因子 :math:`p`.
不可能是 :math:`p = 3` 的情况；
由于 :math:`p` 整除 :math:`4 \prod_{i = 2}^k p_i + 3`,
若 :math:`p` 等于 3, 则它也整除 :math:`\prod_{i = 2}^k p_i`,
这意味着 :math:`p` 等于 :math:`p_i`, :math:`i = 2, \ldots, k` 中的一个；
而我们已经在这个列表中去掉了 3.
因此 :math:`p` 只能是其余元素 :math:`p_i` 中的一个。
但在那种情况下，:math:`p` 整除 :math:`4 \prod_{i = 2}^k p_i`,
从而整除 3, 这和它不是 3 矛盾。

在 Lean 中，记号 ``n % m`` 读作 "``n`` 模 ``m``,"
表示 ``n`` 除以 ``m`` 的余数。
EXAMPLES: -/
-- QUOTE:
example : 27 % 4 = 3 := by norm_num
-- QUOTE.

/- TEXT:
从此以后，我们可以把语句 "``n`` 模 4 余 3" 表示为 ``n % 4 = 3``.
以下示例和定理总结了我们将在下面需要使用的有关此函数的事实。
第一个具名的定理是通过少量情况进行推理的另一个例证。
在第二个具名定理中，
请记住分号表示后续策略块应用于前一个策略创建的所有目标。
EXAMPLES: -/
-- QUOTE:
example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
  rw [add_comm, Nat.add_mul_mod_self_left]

-- BOTH:
theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
  revert h
  rw [Nat.mul_mod]
  have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
  interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
  have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
  interval_cases n % 4 <;> simp

theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
  apply two_le <;>
    · intro neq
      rw [neq] at h
      norm_num at h
-- QUOTE.

/- TEXT:
我们也需要下列事实，它是说若 ``m`` 是 ``n`` 的一个非平凡因子，
那么 ``n / m`` 也是。
看看你能否使用 ``Nat.div_dvd_of_dvd`` 和 ``Nat.div_lt_self`` 完成证明。
BOTH: -/
-- QUOTE:
theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  constructor
  · exact Nat.div_dvd_of_dvd h₀
  exact Nat.div_lt_self (lt_of_le_of_lt (zero_le _) h₂) h₁
-- QUOTE.

-- BOTH:
/- TEXT:
现在把所有的部分放在一起来证明，
任何模 4 余 3 的数都有一个具有相同性质的素数因子。
BOTH: -/
-- QUOTE:
theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
    ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
  by_cases np : n.Prime
  · use n
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
  have mge2 : 2 ≤ m := by
    apply two_le _ mne1
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
  have : m % 4 = 3 ∨ n / m % 4 = 3 := by
    apply mod_4_eq_3_or_mod_4_eq_3
    rw [neq, h]
  rcases this with h1 | h1
/- EXAMPLES:
  . sorry
  . sorry
SOLUTIONS: -/
  · by_cases mp : m.Prime
    · use m
    rcases ih m mltn h1 mp with ⟨p, pp, pdvd, p4eq⟩
    use p
    exact ⟨pp, pdvd.trans mdvdn, p4eq⟩
  obtain ⟨nmdvdn, nmltn⟩ := aux mdvdn mge2 mltn
  by_cases nmp : (n / m).Prime
  · use n / m
  rcases ih (n / m) nmltn h1 nmp with ⟨p, pp, pdvd, p4eq⟩
  use p
  exact ⟨pp, pdvd.trans nmdvdn, p4eq⟩

-- BOTH:
-- QUOTE.
/- TEXT:
我们已经到了最后阶段。给定一个素数集 ``s``,
我们需要谈论该集合删除 3 (如果存在)的结果。
函数 ``Finset.erase`` 可以处理这个问题。
EXAMPLES: -/
-- QUOTE:
example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  rwa [mem_erase] at h

example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
  simp at h
  assumption
-- QUOTE.

/- TEXT:
我们现在已经准备好证明存在无穷多个模 4 余 3 的素数。
填写下面缺失的部分。
我们的解答路径中使用了 ``Nat.dvd_add_iff_left`` 和 ``Nat.dvd_sub'``.
BOTH: -/
-- QUOTE:
theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
  by_contra h
  push_neg at h
  rcases h with ⟨n, hn⟩
  have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
    apply ex_finset_of_bounded
    use n
    contrapose! hn
    rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
    exact ⟨p, pltn, pp, p4⟩
  rcases this with ⟨s, hs⟩
  have h₁ : ((4 * ∏ i ∈ erase s 3, i) + 3) % 4 = 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [add_comm, Nat.add_mul_mod_self_left]
-- BOTH:
  rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
  have ps : p ∈ s := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    rw [← hs p]
    exact ⟨pp, p4eq⟩
-- BOTH:
  have pne3 : p ≠ 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    intro peq
    rw [peq, ← Nat.dvd_add_iff_left (dvd_refl 3)] at pdvd
    rw [Nat.prime_three.dvd_mul] at pdvd
    norm_num at pdvd
    have : 3 ∈ s.erase 3 := by
      apply mem_of_dvd_prod_primes Nat.prime_three _ pdvd
      intro n
      simp [← hs n]
      tauto
    simp at this
-- BOTH:
  have : p ∣ 4 * ∏ i ∈ erase s 3, i := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply dvd_trans _ (dvd_mul_left _ _)
    apply dvd_prod_of_mem
    simp
    constructor <;> assumption
-- BOTH:
  have : p ∣ 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    convert Nat.dvd_sub' pdvd this
    simp
-- BOTH:
  have : p = 3 := by
/- EXAMPLES:
    sorry
SOLUTIONS: -/
    apply pp.eq_of_dvd_of_prime Nat.prime_three this
-- BOTH:
  contradiction
-- QUOTE.

/- TEXT:
如果你成功完成了证明，那么恭喜你！这是形式化的一个重大成果。
TEXT. -/
-- OMIT:
/-
Later:
o fibonacci numbers
o binomial coefficients

(The former is a good example of having more than one base case.)

TODO: mention ``local attribute`` at some point.
-/
