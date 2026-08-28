import Mathlib

/-!
# 4A_AbstractAnalysis：分析的形式化

本文件与同目录下的五章讲义逐节对应。声明前的 `#check` 用来提供可悬浮查询的
Mathlib 入口；`example` 则固定讲义中反复使用的类型与基本推理。

重点不是重建 Mathlib 的分析理论，而是展示同一个 `Filter.Tendsto` 如何承载
点极限、数列极限、无穷远、单侧极限、连续性以及测度论中的最终性。
-/

open Set Filter Topology
open scoped Topology Filter BigOperators ENNReal NNReal

namespace AbstractAnalysis4A

noncomputable section

/-! ## 第一章：从实数极限到度量与拓扑

本章只演示一条抽象链：绝对值、距离、开球、邻域。Filter 与无穷方向留到后续章节。
-/

section Chapter1

section MetricLayer

#check MetricSpace
#check dist
#check Metric.ball

-- 距离小于半径正是落在开球中。
example {X : Type*} [MetricSpace X] (x y : X) (r : ℝ) :
    y ∈ Metric.ball x r ↔ dist y x < r := by
  simp

-- 实数只是带有标准度量的一个实例；同一接口不依赖具体类型。
example (x y : ℝ) : dist x y = |x - y| := by
  simp [Real.dist_eq]

end MetricLayer

section TopologicalLayer

#check TopologicalSpace
#check IsOpen
#check nhds
#check ContinuousAt
#check ContinuousWithinAt
#check ContinuousOn
#check Continuous
#check ContinuousAt.comp

variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {f : X → Y} {g : Y → Z} {x : X}

-- 连续映射复合只使用拓扑与邻域，不需要度量。
example (hg : ContinuousAt g (f x)) (hf : ContinuousAt f x) :
    ContinuousAt (g ∘ f) x :=
  hg.comp hf

end TopologicalLayer

end Chapter1

/-! ## 第二章：Filter 的定义、逻辑与统一极限 -/

section Chapter2

universe u v

section FilterDefinition

variable {α : Type u}

#check Filter
#check Filter.sets
#check Filter.univ_sets
#check Filter.sets_of_superset
#check Filter.inter_sets
#check Filter.Eventually
#check Filter.Frequently

-- Filter α 对任意 α 都组成完备格；退化滤子使任意上下确界总有定义。
#synth CompleteLattice (Filter α)

-- 实数只保证有界非空集合的上确界/下确界，是条件完备的线性序。
#synth ConditionallyCompleteLinearOrder ℝ

end FilterDefinition

section PrincipalAndPure

variable {α : Type u} (s t : Set α) (a b : α)

#check Filter.principal
#check pure
#check mem_principal
#check mem_pure

example : s ∈ (Filter.principal s : Filter α) := by
  exact mem_principal.mpr Set.Subset.rfl

example : s ∈ (pure a : Filter α) ↔ a ∈ s := by
  simp

-- principal 把集合的交并精确送到滤子格的交并。
example : (Filter.principal s ⊓ Filter.principal t : Filter α) =
    Filter.principal (s ∩ t) :=
  inf_principal

example : (Filter.principal s ⊔ Filter.principal t : Filter α) =
    Filter.principal (s ∪ t) :=
  sup_principal

-- 两个不同的固定点要求不能同时满足，因此下确界退化。
example (h : a ≠ b) : (pure a ⊓ pure b : Filter α) = ⊥ := by
  rw [← principal_singleton a, ← principal_singleton b, inf_principal]
  simp [h]

-- 上确界表示命题需要在 a、b 两点共同成立。
example : (pure a ⊔ pure b : Filter α) = Filter.principal ({a, b} : Set α) := by
  rw [← principal_singleton a, ← principal_singleton b, sup_principal]
  congr 1

end PrincipalAndPure

section OrderAndLattice

variable {α : Type u} (F G : Filter α) (P : α → Prop)

#check Filter.le_def
#check Filter.mem_inf_iff_superset
#check Filter.mem_sup
#check Filter.inf_principal
#check Filter.sup_principal
#check Filter.mem_top
#check Filter.mem_bot

-- 顶滤子只接受全称成立的命题。
example : (∀ᶠ x in (⊤ : Filter α), P x) ↔ ∀ x, P x :=
  eventually_top

-- 底滤子接受任意 eventually 命题，包括 False。
example : ∀ᶠ x in (⊥ : Filter α), P x :=
  eventually_bot

example : ∀ᶠ _x in (⊥ : Filter α), False :=
  eventually_bot

-- 滤子序与 eventually 集合族的包含方向相反。
example : F ≤ G ↔ ∀ s ∈ G, s ∈ F :=
  Filter.le_def

end OrderAndLattice

section NeBot

variable {α : Type u} (F : Filter α) (s : Set α)

#check Filter.NeBot
#check Filter.neBot_iff
#check Filter.principal_neBot_iff
#check mem_closure_iff_nhdsWithin_neBot

example : NeBot (Filter.principal s) ↔ s.Nonempty :=
  principal_neBot_iff

example [F.NeBot] : F ≠ ⊥ :=
  Filter.neBot_iff.mp (by infer_instance)

end NeBot

section NeighborhoodFilters

variable {α : Type u} [TopologicalSpace α]
variable (a : α) (S : Set α)

#check (𝓝 a : Filter α)
#check (𝓝[S] a : Filter α)
#check (𝓝[≠] a : Filter α)
#check nhdsWithin

-- nhdsWithin 同时施加“靠近 a”与“位于 S”两个要求。
example : 𝓝[S] a = 𝓝 a ⊓ Filter.principal S :=
  rfl

section OrderedNeighborhoods

variable (x : ℝ)

#check (𝓝[>] x : Filter ℝ)
#check (𝓝[<] x : Filter ℝ)
#check (𝓝[≥] x : Filter ℝ)
#check (𝓝[≤] x : Filter ℝ)
#check nhdsLT_sup_nhdsGT

-- 实线上的去心邻域由左、右两个源滤子的上确界组成。
example : 𝓝[<] x ⊔ 𝓝[>] x = 𝓝[≠] x :=
  nhdsLT_sup_nhdsGT x

end OrderedNeighborhoods

end NeighborhoodFilters

section AtTopAndAtBot

#check (atTop : Filter ℕ)
#check (atTop : Filter ℝ)
#check (atBot : Filter ℤ)
#check (atBot : Filter ℝ)
#check Filter.eventually_atTop
#check Filter.eventually_atBot
#check tendsto_atTop_atTop

-- 对充分大的自然数成立。
example : ∀ᶠ n in (atTop : Filter ℕ), 100 ≤ n :=
  eventually_ge_atTop 100

-- 对充分小的实数成立。
example : ∀ᶠ x in (atBot : Filter ℝ), x < 0 :=
  eventually_lt_atBot 0

end AtTopAndAtBot

section ExtendedValues

-- 扩充值域把无穷作为实际点；它与定义在原类型上的 atTop 是两种不同建模。
#check ENat
#check (⊤ : ℕ∞)
#check ENat.tendsto_nhds_top_iff_natCast_lt
#check ENNReal
#check (⊤ : ℝ≥0∞)
#check ENNReal.tendsto_nhds_top_iff_nat
#check ENNReal.tendsto_nat_nhds_top
#check EReal
#check (⊤ : EReal)
#check EReal.tendsto_coe_nhds_top_iff

end ExtendedValues

section EventuallyAndFrequently

variable {α : Type u} [TopologicalSpace α]
variable (F : Filter α) (P Q : α → Prop) (s : Set α) (x : α)

#check Filter.Eventually.of_forall
#check Filter.Eventually.mono
#check Filter.Eventually.and

example (hP : ∀ᶠ y in F, P y) (hPQ : ∀ᶠ y in F, P y → Q y) :
    ∀ᶠ y in F, Q y := by
  filter_upwards [hP, hPQ] with y hy hyq
  exact hyq hy

example (hP : ∀ᶠ y in F, P y) (hQ : ∀ᶠ y in F, Q y) :
    ∀ᶠ y in F, P y ∧ Q y := by
  filter_upwards [hP, hQ] with y hyP hyQ
  exact ⟨hyP, hyQ⟩

#check mem_closure_iff_frequently

-- 闭包的正确刻画是 frequently 命中 S，而不是点本身必须属于 S。
example : x ∈ closure s ↔ ∃ᶠ y in 𝓝 x, y ∈ s :=
  mem_closure_iff_frequently

-- Frequently 的定义就是“否定 eventually 不成立”。
example : (∃ᶠ y in F, P y) ↔ ¬(∀ᶠ y in F, ¬P y) :=
  Iff.rfl

end EventuallyAndFrequently

section MapComapAndTendsto

variable {α : Type u} {β : Type v} {γ : Type*}
variable (f : α → β) (g : β → γ)
variable (F : Filter α) (G : Filter β) (H : Filter γ)

#check Filter.map
#check Filter.comap
#check Filter.map_map
#check Filter.comap_comap
#check Filter.map_le_iff_le_comap
#check Filter.Tendsto
#check tendsto_def
#check tendsto_iff_eventually
#check tendsto_iff_forall_eventually_mem

example : Tendsto f F G ↔ Filter.map f F ≤ G :=
  Iff.rfl

example (a : α) : Filter.map f (pure a : Filter α) = pure (f a) := by
  simp

-- map 与函数复合相容。
example : Filter.map g (Filter.map f F) = Filter.map (g ∘ f) F :=
  Filter.map_map

-- map/comap 构成 Galois 连接。
example : Filter.map f F ≤ G ↔ F ≤ Filter.comap f G :=
  Filter.map_le_iff_le_comap

-- Tendsto 的复合就是 map 复合与滤子序传递的结构化结果。
example (hf : Tendsto f F G) (hg : Tendsto g G H) :
    Tendsto (g ∘ f) F H :=
  hg.comp hf

end MapComapAndTendsto

section EventuallyEqAndGerms

variable {α : Type u} {β : Type v}
variable (F : Filter α) (f g : α → β)

#check Filter.EventuallyEq
#check Filter.EventuallyLE
#check Filter.Germ
#check tendsto_congr'
#check Filter.Tendsto.congr'
#check Filter.EventuallyEq.tendsto

example : f =ᶠ[F] g ↔ ∀ᶠ x in F, f x = g x :=
  Iff.rfl

-- 一个只在 n = 0 处修改过的数列，与原数列在 atTop 下最终相等。
def changedAtZero (n : ℕ) : ℝ :=
  if n = 0 then 1000 else 1 / (n : ℝ)

def reciprocalNat (n : ℕ) : ℝ :=
  1 / (n : ℝ)

example : changedAtZero =ᶠ[atTop] reciprocalNat := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)
  simp [changedAtZero, reciprocalNat, hn0]

-- 在去心邻域中，点 a 本身可以被忽略。
example [TopologicalSpace α] (a : α) (h : ∀ x, x ≠ a → f x = g x) :
    f =ᶠ[𝓝[≠] a] g := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact h x (by simpa using hx)

end EventuallyEqAndGerms

section EventuallyLEAndAsymptotics

variable {α : Type u}

example : (fun n : ℕ ↦ n) ≤ᶠ[atTop] (fun n ↦ n + 1) :=
  Eventually.of_forall Nat.le_succ

open Asymptotics

variable {E : Type*} [NormedAddCommGroup E]
variable (F : Filter α) (f g : α → E)

#check Asymptotics.IsBigO
#check Asymptotics.IsLittleO
#check (f =O[F] g)
#check (f =o[F] g)

-- Big-O 的最小例子：任意函数都由自身最终支配。
example : f =O[F] f :=
  isBigO_refl f F

-- 同一渐近关系可把 atTop 或局部邻域作为参数。
#check ((fun n : ℕ ↦ (n : ℝ)) =O[atTop] (fun n ↦ (n : ℝ)))
#check ((fun x : ℝ ↦ Real.sin x) =O[𝓝 0] (fun x ↦ x))

end EventuallyLEAndAsymptotics

end Chapter2

/-! ## 第三章：常见极限与连续性的统一形式 -/

section Chapter3

section MetricExpansion

variable {α β : Type*} [PseudoMetricSpace β]
variable {l : Filter α} {u : α → β} {b : β}

-- 只展开目标度量邻域，源滤子仍可保持抽象。
example : Tendsto u l (𝓝 b) ↔
    ∀ ε > 0, ∀ᶠ x in l, dist (u x) b < ε :=
  Metric.tendsto_nhds

variable {X : Type*} [PseudoMetricSpace X]
variable {f : X → β} {a : X}

-- 同时展开源、目标邻域，就得到严格的 epsilon-delta 量词。
#check Metric.tendsto_nhds_nhds
#check Metric.tendsto_nhdsWithin_nhds
#check Metric.continuousAt_iff

end MetricExpansion

section StandardLimits

variable (u : ℕ → ℝ) (f : ℝ → ℝ) (a L : ℝ)

-- 数列极限。
#check (Tendsto u atTop (𝓝 L))

-- 普通连续性、去心极限、集合内极限。
#check (Tendsto f (𝓝 a) (𝓝 (f a)))
#check (Tendsto f (𝓝[≠] a) (𝓝 L))
#check (Tendsto f (𝓝[Set.Ici a] a) (𝓝 L))

-- 右极限与左极限。
#check (Tendsto f (𝓝[>] a) (𝓝 L))
#check (Tendsto f (𝓝[<] a) (𝓝 L))

-- 源趋于无穷与目标趋于无穷。
#check (Tendsto f atTop (𝓝 L))
#check (Tendsto f atBot (𝓝 L))
#check (Tendsto f (𝓝 a) atTop)
#check (Tendsto f atTop atTop)

-- 讲义中的 1/(n+1) 数列极限。
example : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

-- x^2 在 x → +∞ 时趋于 +∞。
example : Tendsto (fun x : ℝ ↦ x ^ 2) atTop atTop := by
  exact tendsto_pow_atTop (by norm_num)

end StandardLimits

section OneSidedLimits

variable (f : ℝ → ℝ) (a L : ℝ)

-- 两侧极限等价于左、右极限同时存在且取同一值。
example : Tendsto f (𝓝[≠] a) (𝓝 L) ↔
    Tendsto f (𝓝[<] a) (𝓝 L) ∧ Tendsto f (𝓝[>] a) (𝓝 L) := by
  rw [← nhdsLT_sup_nhdsGT a, tendsto_sup]

end OneSidedLimits

section Continuity

variable {X Y Z : Type*}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
variable {f : X → Y} {g : Y → Z} {x : X}

-- ContinuousAt 的定义就是两个邻域滤子之间的 Tendsto。
example : ContinuousAt f x ↔ Tendsto f (𝓝 x) (𝓝 (f x)) :=
  Iff.rfl

example (hf : ContinuousAt f x) (hg : ContinuousAt g (f x)) :
    ContinuousAt (g ∘ f) x :=
  hg.comp hf

end Continuity

section LimitUniqueness

variable {α X : Type*} [TopologicalSpace X] [T2Space X]
variable {l : Filter α} [l.NeBot] {f : α → X} {a b : X}

#check tendsto_nhds_unique

example (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb

end LimitUniqueness

end Chapter3

/-! ## 第四章：Fréchet 导数与链式法则 -/

section Chapter4

section FrechetDerivative

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]

#check ContinuousLinearMap
#check HasFDerivAt
#check HasFDerivAtFilter
#check HasFDerivAt.comp
#check hasFDerivAt_id

variable {f : E → F} {g : F → G} {f' : E →L[𝕜] F} {g' : F →L[𝕜] G} {x : E}

-- Fréchet 链式法则中的导数是连续线性映射的复合。
example (hf : HasFDerivAt f f' x) (hg : HasFDerivAt g g' (f x)) :
    HasFDerivAt (g ∘ f) (g'.comp f') x :=
  hg.comp x hf

-- 连续线性映射在每一点的导数就是自身。
example (A : E →L[𝕜] F) (x : E) : HasFDerivAt A A x :=
  A.hasFDerivAt

end FrechetDerivative

section OneDimensionalDerivative

#check HasDerivAt
#check hasDerivAt_id
#check hasDerivAt_const
#check hasDerivAt_pow
#check Real.hasDerivAt_exp
#check Real.hasDerivAt_sin
#check Real.hasDerivAt_cos
#check HasDerivAt.add
#check HasDerivAt.mul
#check HasDerivAt.comp

variable {f g : ℝ → ℝ} {f' g' x : ℝ}

-- (g ∘ f)'(x) = g'(f x) * f'(x) 的结构化版本。
example (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' (f x)) :
    HasDerivAt (g ∘ f) (g' * f') x :=
  hg.comp x hf

-- 由平方函数与 sin 的原子导数定理组合得到 sin(x^2) 的导数。
example (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.sin (y ^ 2)) (Real.cos (x ^ 2) * (2 * x)) x := by
  simpa [Function.comp_def] using
    (Real.hasDerivAt_sin (x ^ 2)).comp x (hasDerivAt_pow 2 x)

end OneDimensionalDerivative

end Chapter4

/-! ## 第五章：测度、几乎处处与控制收敛 -/

section Chapter5

open MeasureTheory

section MeasuresAndAE

variable {α : Type*} [MeasurableSpace α]
variable (μ : Measure α)

#check Measure
#check Measure.dirac
#check Measure.count
#check volume
#check MeasureTheory.ae
#check MeasureTheory.ae_iff

variable (P : α → Prop)

-- ae μ 是一个滤子；其 eventually 集合的补集具有零测度。
example : (∀ᵐ x ∂μ, P x) ↔ μ {x | ¬P x} = 0 :=
  ae_iff

end MeasuresAndAE

section IntegralAndIntegrable

variable {α E : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (μ : Measure α) (f : α → E)

#check MeasureTheory.integral
#check MeasureTheory.Integrable
#check MeasureTheory.AEStronglyMeasurable
#check MeasureTheory.HasFiniteIntegral
#check MeasureTheory.integral_congr_ae

-- Integrable 严格由“几乎处处强可测”和“范数积分有限”组成。
example : Integrable f μ ↔ AEStronglyMeasurable f μ ∧ HasFiniteIntegral f μ :=
  Iff.rfl

-- 几乎处处相等的函数具有相同积分。
example {g : α → E} (h : f =ᵐ[μ] g) :
    (∫ x, f x ∂μ) = ∫ x, g x ∂μ :=
  integral_congr_ae h

end IntegralAndIntegrable

section DominatedConvergence

variable {α G : Type*} [MeasurableSpace α]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {μ : Measure α} {F : ℕ → α → G} {f : α → G}

#check MeasureTheory.tendsto_integral_of_dominated_convergence
#check MeasureTheory.tendsto_integral_filter_of_dominated_convergence
#check MeasureTheory.hasFiniteIntegral_of_dominated_convergence

-- 控制收敛：外层 ae μ 与内层 atTop 同时出现在一个严格类型化陈述中。
example (bound : α → ℝ)
    (F_measurable : ∀ n, AEStronglyMeasurable (F n) μ)
    (bound_integrable : Integrable bound μ)
    (h_bound : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound x)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun n ↦ F n x) atTop (𝓝 (f x))) :
    Tendsto (fun n ↦ ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) :=
  tendsto_integral_of_dominated_convergence
    bound F_measurable bound_integrable h_bound h_lim

end DominatedConvergence

end Chapter5

end

end AbstractAnalysis4A
