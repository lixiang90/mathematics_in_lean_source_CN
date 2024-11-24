-- BOTH:
import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

/- TEXT:
.. _proving_facts_about_algebraic_structures:

证明关于代数结构的事实
----------------------------------------

.. index:: order relation, partial order

在 :numref:`proving_identities_in_algebraic_structures` 中，我们看到许多关于实数的常见恒等式适用于更一般的代数结构类，比如交换环。
我们可以使用任何我们想要的公理描述代数结构，而不是仅仅用方程式。
例如，*偏序* 包括一个具有二元关系的集合，该关系是自反的、传递的和反对称的，就像实数上的 ``≤``。Lean 知道偏序：
TEXT. -/
section
-- QUOTE:
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

-- EXAMPLES:
#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

-- QUOTE.

/- TEXT:
在这里，我们采用了 Mathlib 的惯例，使用诸如 ``α``、 ``β`` 和 ``γ`` 这样的字母（用 ``\a``、``\b`` 和 ``\g`` 输入）表示任意类型。
该库通常使用诸如 ``R`` 和 ``G`` 这样的字母来表示代数结构（如环和群）的载体，但是一般希腊字母用于类型，特别是当它们与很少或没有结构与之关联时。

对于任何偏序 ``≤``，还有一个 *严格偏序* ``<``，它的行为有点像实数上的 ``<``. 说 ``x`` 在此顺序中小于 ``y`` 等价于说它小于或等于 ``y``，但不等于 ``y``.
TEXT. -/
-- QUOTE:
#check x < y
#check (lt_irrefl x : ¬ (x < x))
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne
-- QUOTE.

end

/- TEXT:
在这个例子中，符号 ``∧`` 表示 "and"，符号 ``¬`` 表示 "not"，而 ``x ≠ y`` 是 ``¬ (x = y)`` 的缩写。
在 :numref:`Chapter %s <logic>` 中，你将学习如何使用这些逻辑连接词来 *证明* ``<`` 具有所示的属性。

.. index:: lattice

一个 *格* 是将偏序扩展为具有运算符 ``⊓`` 和 ``⊔`` 的结构，这些运算符类似于实数上的 ``min`` 和 ``max``：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [Lattice α]
variable (x y z : α)

-- EXAMPLES:
#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
-- QUOTE.

/- TEXT:
**⊓** 和 **⊔** 的特征使得我们可以合理地称它们为 *最大下界* 和 *最小上界*。
在 VS Code 中，你可以使用 **\glb** 和 **\lub** 输入它们。这些符号通常也称为 *下确界* 和 *上确界*，在 Mathlib 中，它们在定理名称中被记为 **inf** 和 **sup**。
更复杂的是，它们也经常被称为 *meet* 和 *join*。因此，如果你使用格，需要记住以下字典：

* ``⊓`` 是 *最大下界*、*下确界* 或 *meet*.

* ``⊔`` 是 *最小上界*、*上确界* 或 *join*.

一些格的实例包括：

* 任何全序上的 ``min`` 和 ``max``，例如带有 ``≤`` 的整数或实数

* 某个域的子集合的 ``∩`` 和 ``∪``，其中的序是 ``⊆``

* 布尔真值的 ``∧`` 和 ``∨``，其中的序是如果 ``x`` 是假或 ``y`` 是真，则 ``x ≤ y``

* 自然数（或正自然数）上的 ``gcd`` 和 ``lcm``，其中的排序是 ``∣``

* 向量空间的线性子空间的集合，其中最大下界由交集给出，最小上界由两个空间的和给出，并且序是包含关系

* 一个集合（或在 Lean 中，一个类型）上的拓扑的集合，其中两个拓扑的最大下界由它们的并集生成的拓扑给出，最小上界是它们的交集，并且排序是逆包含关系

你可以验证，与 ``min`` / ``max`` 和 ``gcd`` / ``lcm`` 一样，你可以仅使用刻画它们的公理以及 ``le_refl`` 和 ``le_trans`` 来证明下确界和上确界的交换性和结合性。

.. index:: trans, tactics ; trans

当看到目标 ``x ≤ z`` 时使用 ``apply le_trans`` 不是个好主意。
事实上 Lean 无法猜测我们想使用哪个中间元素 ``y``.
因此 ``apply le_trans`` 产生形如 ``x ≤ ?a``, ``?a ≤ z``
以及 ``α`` 的三个目标，其中 ``?a`` （也可能有一个更复杂的、自动生成的名字）表示神秘的 ``y``.
最后的目标具有类型 ``α``, 用于提供 ``y`` 的值。
它之所以出现在最后，是因为 Lean 希望从第一个目标 ``x ≤ ?a`` 的证明中自动推断它。
为了避免这种令人不快的情况，
你可以使用 ``calc`` 策略提供精确的 ``y``.
或者，你也可以使用 ``trans`` 策略，
它将 ``y`` 作为参数，产生期望的目标 ``x ≤ y`` 和 ``y ≤ z``.
当然，你也可以通过直接提供完整的证明来避免这个问题，例如
``exact le_trans inf_le_left inf_le_right``, 但这需要更多规划。
TEXT. -/
-- QUOTE:
example : x ⊓ y = y ⊓ x := by
  sorry

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  sorry

example : x ⊔ y = y ⊔ x := by
  sorry

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example : x ⊓ y = y ⊓ x := by
  apply le_antisymm
  repeat
    apply le_inf
    · apply inf_le_right
    apply inf_le_left

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  · apply le_inf
    · trans x ⊓ y
      apply inf_le_left
      apply inf_le_left
    apply le_inf
    · trans x ⊓ y
      apply inf_le_left
      apply inf_le_right
    apply inf_le_right
  apply le_inf
  · apply le_inf
    · apply inf_le_left
    trans y ⊓ z
    apply inf_le_right
    apply inf_le_left
  trans y ⊓ z
  apply inf_le_right
  apply inf_le_right

example : x ⊔ y = y ⊔ x := by
  apply le_antisymm
  repeat
    apply sup_le
    · apply le_sup_right
    apply le_sup_left

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      apply le_sup_left
      · trans y ⊔ z
        apply le_sup_left
        apply le_sup_right
    trans y ⊔ z
    apply le_sup_right
    apply le_sup_right
  apply sup_le
  · trans x ⊔ y
    apply le_sup_left
    apply le_sup_left
  apply sup_le
  · trans x ⊔ y
    apply le_sup_right
    apply le_sup_left
  apply le_sup_right

/- TEXT:
你可以在 Mathlib 中找到这些定理，它们分别是 ``inf_comm``、``inf_assoc``、``sup_comm`` 和 ``sup_assoc``.

另一个很好的练习是仅使用这些公理证明 *吸收律*：
TEXT. -/
-- QUOTE:
theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  sorry

theorem absorb2 : x ⊔ x ⊓ y = x := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem absorb1αα : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  · apply inf_le_left
  apply le_inf
  · apply le_refl
  apply le_sup_left

theorem absorb2αα : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  · apply sup_le
    · apply le_refl
    apply inf_le_left
  apply le_sup_left

-- BOTH:
end

/- TEXT:
这些定理可以在 Mathlib 中找到，其名称分别为 ``inf_sup_self`` 和 ``sup_inf_self``.

一个满足额外恒等式 ``x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)`` 和 ``x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)`` 的格，称为 *分配格*。Lean 也知道这些：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
-- QUOTE.
end

/- TEXT:
左右两个版本容易证明是等价的，鉴于 ``⊓`` 和 ``⊔`` 的交换律。一个很好的练习是通过提供一个具有有限个元素的非分配格的显式描述，展示并非每个格都是分配格。
还有一个很好的练习是证明在任何格中，任一分配律可以推导出另一个分配律。
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {α : Type*} [Lattice α]
variable (a b c : α)

-- EXAMPLES:
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  rw [h, @inf_comm _ _ (a ⊔ b), absorb1, @inf_comm _ _ (a ⊔ b), h, ← sup_assoc, @inf_comm _ _ c a,
    absorb2, inf_comm]

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  rw [h, @sup_comm _ _ (a ⊓ b), absorb2, @sup_comm _ _ (a ⊓ b), h, ← inf_assoc, @sup_comm _ _ c a,
    absorb1, sup_comm]

-- BOTH:
end

/- TEXT:
可以将公理结构组合成更大的结构。例如，*严格有序环* 由一个交换环和相应载体集上的一个偏序组成，满足额外的公理，这些公理表明环运算与序是兼容的：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

-- EXAMPLES:
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)
-- QUOTE.

/- TEXT:
:numref:`Chapter %s <logic>` 将提供从 ``mul_pos`` 和 ``<`` 的定义中得出以下定理的方式：
TEXT. -/
-- QUOTE:
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
-- QUOTE.

/- TEXT:
这是一个拓展练习，展示了许多用于推理关于实数上的算术和序的常见事实，通用于任何有序环。
下面是你可以尝试的一些示例，仅使用环、偏序以及上面两个示例中列举的事实（注意到这些环不被假定为交换的，所以 `ring` 策略不可用）：
TEXT. -/
-- QUOTE:
example (h : a ≤ b) : 0 ≤ b - a := by
  sorry

example (h: 0 ≤ b - a) : a ≤ b := by
  sorry

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry
-- QUOTE.

-- SOLUTIONS:
theorem aux1 (h : a ≤ b) : 0 ≤ b - a := by
  rw [← sub_self a, sub_eq_add_neg, sub_eq_add_neg, add_comm, add_comm b]
  apply add_le_add_left h

theorem aux2 (h : 0 ≤ b - a) : a ≤ b := by
  rw [← add_zero a, ← sub_add_cancel b a, add_comm (b - a)]
  apply add_le_add_left h

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  have h1 : 0 ≤ (b - a) * c := mul_nonneg (aux1 _ _ h) h'
  rw [sub_mul] at h1
  exact aux2 _ _ h1

-- BOTH:
end

/- TEXT:
.. index:: metric space

最后，这是最后一个例子。
*度量空间* 由一个配备了距离概念的集合组成，``dist x y``,
将任何一对元素映射到一个实数。
距离函数被假设满足以下公理：
TEXT. -/
-- BOTH:
section
-- QUOTE:
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

-- EXAMPLES:
#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)
-- QUOTE.

/- TEXT:
掌握了本节内容后，你可以利用以上公理证明距离始终是非负的：
TEXT. -/
-- QUOTE:
example (x y : X) : 0 ≤ dist x y := by
  sorry
-- QUOTE.

-- SOLUTIONS:
example (x y : X) : 0 ≤ dist x y :=by
  have : 0 ≤ dist x y + dist y x := by
    rw [← dist_self x]
    apply dist_triangle
  linarith [dist_comm x y]

-- BOTH:
end

/- TEXT:
我们建议利用 `nonneg_of_mul_nonneg_left` 完成这个定理的证明。正如你可能已经猜到的那样，在Mathlib中这个定理被称为 `dist_nonneg` .
TEXT. -/
