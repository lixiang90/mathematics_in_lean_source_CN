-- BOTH:
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.Parity
import MIL.Common

/- TEXT:
.. _sets:

集合
----

.. index:: set operations

若 ``α`` 是任意类型，则类型 ``Set α`` 由 ``α`` 中的元素组成的集合构成。
这一类型支持常规的集合论运算和关系。
例如， ``s ⊆ t`` 是说 ``s`` 是 ``t`` 的子集，
``s ∩ t`` 是指 ``s`` 和 ``t`` 的交集，
而 ``s ∪ t`` 是指它们的并集。
子集关系可以用 ``\ss`` 或 ``\sub`` 输入，
交集可以用 ``\i`` 或 ``\cap`` 输入，
并集可以用 ``\un`` 或 ``\cup`` 输入。
库中也定义了集合 ``univ``,
它包含类型 ``α`` 的全部元素，
以及空集 ``∅``, 可以用 ``\empty`` 输入。
给定 ``x : α`` 和 ``s : Set α``,
表达式 ``x ∈ s`` 是说 ``x`` 是 ``s`` 的一个成员。
提到集合成员关系的定理的名字经常含有 ``mem``.
表达式 ``x ∉ s`` 是 ``¬ x ∈ s`` 的缩写。
你可以用 ``\in`` 或 ``\mem`` 输入 ``∈``, 用 ``\notin`` 输入 ``∉``.

.. index:: simp, tactics ; simp

证明关于集合的事情的一种方法是使用 ``rw`` 或化简器来展开定义。
在下面的第二个例子中， 我们使用 ``simp only`` 告诉化简器只使用我们给它的列表中的等式，
而不是整个数据库中的等式。
不同于 ``rw``, ``simp`` 可以在全称或存在量词内实施化简。
如果你逐步查看证明，你可以看到这些命令的效果。
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*}
variable (s t u : Set α)
open Set

-- EXAMPLES:
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def, inter_def, inter_def]
  rw [subset_def] at h
  simp only [mem_setOf]
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  simp only [subset_def, mem_inter_iff] at *
  rintro x ⟨xs, xu⟩
  exact ⟨h _ xs, xu⟩
-- QUOTE.

/- TEXT:
在这个例子中，我们开启了 ``Set`` 名字空间以用更短的定理名访问定理。
但事实上，我们可以完全删除 ``rw`` 和 ``simp`` 的调用：
TEXT. -/
-- QUOTE:
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x xsu
  exact ⟨h xsu.1, xsu.2⟩
-- QUOTE.

/- TEXT:
这里发生的事情被称为 *定义约化*：为了理解 ``intro`` 命令和匿名构造函数，
Lean 不得不展开定义。
下面的例子也说明了这一现象：
TEXT. -/
-- QUOTE:
example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
  fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩
-- QUOTE.

/- TEXT:
为了处理并集，我们可以使用 ``Set.union_def`` 和 ``Set.mem_union``.
由于 ``x ∈ s ∪ t`` 展开为 ``x ∈ s ∨ x ∈ t``,
我们也可以使用 ``cases`` 策略强制要求定义约化。
TEXT. -/
-- QUOTE:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  intro x hx
  have xs : x ∈ s := hx.1
  have xtu : x ∈ t ∪ u := hx.2
  rcases xtu with xt | xu
  · left
    show x ∈ s ∩ t
    exact ⟨xs, xt⟩
  . right
    show x ∈ s ∩ u
    exact ⟨xs, xu⟩
-- QUOTE.

/- TEXT:
由于交集比联合更紧密，
表达式 ``(s ∩ t) ∪ (s ∩ u)`` 中使用括号是不必要的，
但它们使表达式的含义更清晰。
下面是对同一事实更简短的证明：
TEXT. -/
-- QUOTE:
example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
  rintro x ⟨xs, xt | xu⟩
  · left; exact ⟨xs, xt⟩
  . right; exact ⟨xs, xu⟩
-- QUOTE.

/- TEXT:
作为练习，试着证明另一方向的包含关系：
BOTH: -/
-- QUOTE:
example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rintro x (⟨xs, xt⟩ | ⟨xs, xu⟩)
  · use xs; left; exact xt
  . use xs; right; exact xu
-- QUOTE.

-- BOTH:
/- TEXT:
知道以下事实可能有帮助：当使用 ``rintro`` 时，
有时我们需要使用括号包围析取模式 ``h1 | h2`` 使得 Lean 能正确解析它。

库里也定义了集合的差， ``s \ t``,
其中反斜线是以 ``\\`` 输入的特殊unicode字符。
表达式 ``x ∈ s \ t`` 展开为 ``x ∈ s ∧ x ∉ t``.
（ ``∉`` 可以用 ``\notin`` 输入。）
可以使用 ``Set.diff_eq`` 和 ``dsimp`` 或 ``Set.mem_diff`` 手动重写它，
而下面对同一个包含关系的两个证明展示了如何避免使用它们。
TEXT. -/
-- QUOTE:
example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  intro x xstu
  have xs : x ∈ s := xstu.1.1
  have xnt : x ∉ t := xstu.1.2
  have xnu : x ∉ u := xstu.2
  constructor
  · exact xs
  intro xtu
  -- x ∈ t ∨ x ∈ u
  rcases xtu with xt | xu
  · show False; exact xnt xt
  . show False; exact xnu xu

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
  rintro x ⟨⟨xs, xnt⟩, xnu⟩
  use xs
  rintro (xt | xu) <;> contradiction
-- QUOTE.

/- TEXT:
作为练习，证明反向的包含关系：
BOTH: -/
-- QUOTE:
example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
/- EXAMPLES:
  sorry
SOLUTIONS: -/
  rintro x ⟨xs, xntu⟩
  constructor
  use xs
  · intro xt
    exact xntu (Or.inl xt)
  intro xu
  apply xntu (Or.inr xu)
-- QUOTE.

-- BOTH:
/- TEXT:
要证明两个集合相等，
只需证明任一集合中的每个元素都是另一个集合中的元素。
这个原理称为“外延性”，毫不意外的是，
``ext`` 策略可以用于处理它。
TEXT. -/
-- QUOTE:
example : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  . rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩
-- QUOTE.

/- TEXT:
再次重申，删除 ``simp only [mem_inter_iff]`` 一行并不会损害证明。
事实上，如果你喜欢高深莫测的证明项，下面的单行证明就是为你准备的：
TEXT. -/
-- QUOTE:
example : s ∩ t = t ∩ s :=
  Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩
-- QUOTE.

/- TEXT:
这是一个更简短的证明，使用了化简器：
TEXT. -/
-- QUOTE:
example : s ∩ t = t ∩ s := by ext x; simp [and_comm]
-- QUOTE.

/- TEXT:
除了使用 ``ext`` 之外，我们还可以使用 ``Subset.antisymm`` 这个定理，
它可以通过证明 ``s ⊆ t`` 和 ``t ⊆ s`` 来证明集合间的等式 ``s = t``.
TEXT. -/
-- QUOTE:
example : s ∩ t = t ∩ s := by
  apply Subset.antisymm
  · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
  . rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩
-- QUOTE.

/- TEXT:
尝试完成证明项：
BOTH: -/
-- QUOTE:
example : s ∩ t = t ∩ s :=
/- EXAMPLES:
    Subset.antisymm sorry sorry
SOLUTIONS: -/
    Subset.antisymm
    (fun x ⟨xs, xt⟩ ↦ ⟨xt, xs⟩) fun x ⟨xt, xs⟩ ↦ ⟨xs, xt⟩
-- QUOTE.

-- BOTH:
/- TEXT:
请记住，您可以用下划线代替 ``sorry``,
并将鼠标悬停在它上面,
Lean 会向你显示它在这一位置的预期。

下面是一些你可能会喜欢证明的集合论性质：
TEXT. -/
-- QUOTE:
example : s ∩ (s ∪ t) = s := by
  sorry

example : s ∪ s ∩ t = s := by
  sorry

example : s \ t ∪ t = s ∪ t := by
  sorry

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : s ∩ (s ∪ t) = s := by
  ext x; constructor
  · rintro ⟨xs, _⟩
    exact xs
  . intro xs
    use xs; left; exact xs

example : s ∪ s ∩ t = s := by
  ext x; constructor
  · rintro (xs | ⟨xs, xt⟩) <;> exact xs
  . intro xs; left; exact xs

example : s \ t ∪ t = s ∪ t := by
  ext x; constructor
  · rintro (⟨xs, nxt⟩ | xt)
    · left
      exact xs
    . right
      exact xt
  by_cases h : x ∈ t
  · intro
    right
    exact h
  rintro (xs | xt)
  · left
    use xs
  right; exact xt

example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
  ext x; constructor
  · rintro (⟨xs, xnt⟩ | ⟨xt, xns⟩)
    · constructor
      left
      exact xs
      rintro ⟨_, xt⟩
      contradiction
    . constructor
      right
      exact xt
      rintro ⟨xs, _⟩
      contradiction
  rintro ⟨xs | xt, nxst⟩
  · left
    use xs
    intro xt
    apply nxst
    constructor <;> assumption
  . right; use xt; intro xs
    apply nxst
    constructor <;> assumption

/- TEXT:
说到集合的表示，下面就为大家揭秘背后的机制。
在类型论中，类型 ``α`` 上的 *性质* 或 *谓词* 只是一个函数 ``P : α → Prop``.
这是有意义的：给定 ``a : α``,  ``P a`` 就是 ``P`` 对 ``a`` 成立这一命题。
在库中， ``Set α`` 定义为 ``α → Prop`` 而 ``x ∈ s`` 定义为 ``s x``.
换句话说，集合实际上就是性质，只是被当成对象。

库中也定义了集合构造器的符号。
表达式 ``{ y | P y }`` 展开就是 ``(fun y ↦ P y)``,
因此 ``x ∈ { y | P y }`` 约化为 ``P x``.
因此我们可以把偶数性质转化为偶数集合：
TEXT. -/
-- QUOTE:
def evens : Set ℕ :=
  { n | Even n }

def odds : Set ℕ :=
  { n | ¬Even n }

example : evens ∪ odds = univ := by
  rw [evens, odds]
  ext n
  simp
  apply Classical.em
-- QUOTE.

/- TEXT:
You should step through this proof and make sure
you understand what is going on.
Try deleting the line ``rw [evens, odds]``
and confirm that the proof still works.

In fact, set-builder notation is used to define

- ``s ∩ t`` as ``{x | x ∈ s ∧ x ∈ t}``,
- ``s ∪ t`` as ``{x | x ∈ s ∨ x ∈ t}``,
- ``∅`` as ``{x | False}``, and
- ``univ`` as ``{x | True}``.

We often need to indicate the type of ``∅`` and ``univ``
explicitly,
because Lean has trouble guessing which ones we mean.
The following examples show how Lean unfolds the last
two definitions when needed. In the second one,
``trivial`` is the canonical proof of ``True`` in the library.
TEXT. -/
-- QUOTE:
example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
  h

example (x : ℕ) : x ∈ (univ : Set ℕ) :=
  trivial
-- QUOTE.

/- TEXT:
As an exercise, prove the following inclusion.
Use ``intro n`` to unfold the definition of subset,
and use the simplifier to reduce the
set-theoretic constructions to logic.
We also recommend using the theorems
``Nat.Prime.eq_two_or_odd`` and ``Nat.even_iff``.
TEXT. -/
-- QUOTE:
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
  intro n
  simp
  intro nprime
  rcases Nat.Prime.eq_two_or_odd nprime with h | h
  · rw [h]
    intro
    linarith
  rw [Nat.even_iff, h]
  norm_num

/- TEXT:
Be careful: it is somewhat confusing that the library has multiple versions
of the predicate ``Prime``.
The most general one makes sense in any commutative monoid with a zero element.
The predicate ``Nat.Prime`` is specific to the natural numbers.
Fortunately, there is a theorem that says that in the specific case,
the two notions agree, so you can always rewrite one to the other.
TEXT. -/
-- QUOTE:
#print Prime

#print Nat.Prime

example (n : ℕ) : Prime n ↔ Nat.Prime n :=
  Nat.prime_iff.symm

example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rw [Nat.prime_iff]
  exact h
-- QUOTE.

/- TEXT:
.. index:: rwa, tactics ; rwa

The `rwa` tactic follows a rewrite with the assumption tactic.
TEXT. -/
-- QUOTE:
example (n : ℕ) (h : Prime n) : Nat.Prime n := by
  rwa [Nat.prime_iff]
-- QUOTE.

-- BOTH:
end

/- TEXT:
.. index:: bounded quantifiers

Lean introduces the notation ``∀ x ∈ s, ...``,
"for every ``x`` in ``s`` .,"
as an abbreviation for  ``∀ x, x ∈ s → ...``.
It also introduces the notation ``∃ x ∈ s, ...,``
"there exists an ``x`` in ``s`` such that .."
These are sometimes known as *bounded quantifiers*,
because the construction serves to restrict their significance
to the set ``s``.
As a result, theorems in the library that make use of them
often contain ``ball`` or ``bex`` in the name.
The theorem ``bex_def`` asserts that ``∃ x ∈ s, ...`` is equivalent
to ``∃ x, x ∈ s ∧ ...,``
but when they are used with ``rintro``, ``use``,
and anonymous constructors,
these two expressions behave roughly the same.
As a result, we usually don't need to use ``bex_def``
to transform them explicitly.
Here is are some examples of how they are used:
TEXT. -/
-- BOTH:
section

-- QUOTE:
variable (s t : Set ℕ)

-- EXAMPLES:
example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x xs
  apply h₁ x xs

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
  rcases h with ⟨x, xs, _, prime_x⟩
  use x, xs
-- QUOTE.

/- TEXT:
See if you can prove these slight variations:
TEXT. -/
-- QUOTE:
section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  sorry

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  sorry

end
-- QUOTE.

-- SOLUTIONS:
section
variable (ssubt : s ⊆ t)

example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
  intro x xs
  constructor
  · apply h₀ x (ssubt xs)
  apply h₁ x (ssubt xs)

example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
  rcases h with ⟨x, xs, _, px⟩
  use x, ssubt xs

end

-- BOTH:
end

/- TEXT:
Indexed unions and intersections are
another important set-theoretic construction.
We can model a sequence :math:`A_0, A_1, A_2, \ldots` of sets of
elements of ``α``
as a function ``A : ℕ → Set α``,
in which case ``⋃ i, A i`` denotes their union,
and ``⋂ i, A i`` denotes their intersection.
There is nothing special about the natural numbers here,
so ``ℕ`` can be replaced by any type ``I``
used to index the sets.
The following illustrates their use.
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α I : Type*}
variable (A B : I → Set α)
variable (s : Set α)

open Set

-- EXAMPLES:
example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i
-- QUOTE.

/- TEXT:
Parentheses are often needed with an
indexed union or intersection because,
as with the quantifiers,
the scope of the bound variable extends as far as it can.

Try proving the following identity.
One direction requires classical logic!
We recommend using ``by_cases xs : x ∈ s``
at an appropriate point in the proof.
TEXT. -/
-- QUOTE:

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
  ext x
  simp only [mem_union, mem_iInter]
  constructor
  · rintro (xs | xI)
    · intro i
      right
      exact xs
    intro i
    left
    exact xI i
  intro h
  by_cases xs : x ∈ s
  · left
    exact xs
  right
  intro i
  cases h i
  · assumption
  contradiction

/- TEXT:
Mathlib also has bounded unions and intersections,
which are analogous to the bounded quantifiers.
You can unpack their meaning with ``mem_iUnion₂``
and ``mem_iInter₂``.
As the following examples show,
Lean's simplifier carries out these replacements as well.
TEXT. -/
-- QUOTE:
-- BOTH:
def primes : Set ℕ :=
  { x | Nat.Prime x }

-- EXAMPLES:
example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
  ext
  rw [mem_iUnion₂]
  simp

example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
  ext
  simp

example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
  intro x
  contrapose!
  simp
  apply Nat.exists_prime_and_dvd
-- QUOTE.

/- TEXT:
Try solving the following example, which is similar.
If you start typing ``eq_univ``,
tab completion will tell you that ``apply eq_univ_of_forall``
is a good way to start the proof.
We also recommend using the theorem ``Nat.exists_infinite_primes``.
TEXT. -/
-- QUOTE:
example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
  apply eq_univ_of_forall
  intro x
  simp
  rcases Nat.exists_infinite_primes x with ⟨p, primep, pge⟩
  use p, pge

-- BOTH:
end

/- TEXT:
Give a collection of sets, ``s : Set (Set α)``,
their union, ``⋃₀ s``, has type ``Set α``
and is defined as ``{x | ∃ t ∈ s, x ∈ t}``.
Similarly, their intersection, ``⋂₀ s``, is defined as
``{x | ∀ t ∈ s, x ∈ t}``.
These operations are called ``sUnion`` and ``sInter``, respectively.
The following examples show their relationship to bounded union
and intersection.
TEXT. -/
section

open Set

-- QUOTE:
variable {α : Type*} (s : Set (Set α))

example : ⋃₀ s = ⋃ t ∈ s, t := by
  ext x
  rw [mem_iUnion₂]
  simp

example : ⋂₀ s = ⋂ t ∈ s, t := by
  ext x
  rw [mem_iInter₂]
  rfl
-- QUOTE.

end

/- TEXT:
In the library, these identities are called
``sUnion_eq_biUnion`` and ``sInter_eq_biInter``.
TEXT. -/
