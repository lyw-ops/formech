/-
  `act` 用显式还是隐式：对照实验

  背景：`Mech.type` 原先写作 `structure type {act : Type} (n : ℕ)`，导致每个使用点都要写
  `Mech.type (act := B) n`（原文件里 7 处）。这个文件把两种标注下的同一份内容各写一遍，
  记录它们到底在哪里不同。

  本文件自足，不依赖 formech，可以单独 `lake env lean` 检查。所有结论都由下面的代码实测得出。

  ## 结论

  显式更好，但理由不是"隐式做不到"——两个版本表达力完全相同，下面每个例子两边都能写出来。
  真实差异只有两条：

  1. 每次把 `Mech ... n` 这个类型**写出来**（binder、`variable` 块、返回类型），
     隐式版要多写 `(act := ` 和 `)`，约 9 个字符。这类位置在性质层里会越来越多。
  2. 显式让未决的 metavariable 可见（见文件末尾），隐式会把它藏起来。

  而**创建** mech、投影、应用、通用消费函数的调用点，两边逐字符相同。

  ## 一个常见误解

  "隐式参数可以让 Lean 从定义体里推出 act" —— 不成立。Lean 会先把 `def` / `theorem` 的
  头部类型完全解析完再处理定义体，所以两个版本在这一点上同样无能为力。详见文件末尾
  被注释掉的失败案例。
-/
import Mathlib.Data.Vector.Basic

universe u

instance : HPow (Type u) ℕ (Type u) := ⟨Vector⟩

/- ========================= 版本 I：act 隐式 ========================= -/

namespace Imp

structure Mech {act : Type} (n : ℕ) where
  O : Type
  M : act ^ n → O

structure Prefs {act : Type} {n : ℕ} (m : Mech (act := act) n) where
  V : Fin n → act
  U : Fin n → m.O → ℕ

def Truthful {act : Type} {n : ℕ} {m : Mech (act := act) n} (p : Prefs m) : Prop :=
  ∀ (b b' : act ^ n) (i : Fin n), p.U i (m.M b') ≤ p.U i (m.M b)

/- 例子一：物品给出价最高者（下标最小的那个），act = ℕ -/
def highestBidder (n : ℕ) : Mech (act := ℕ) n where
  O := Option (Fin n)
  M := fun b => Fin.find? fun i => decide (∀ j, b.get j ≤ b.get i)

/- 例子二：0 号 agent 独裁。act = Fin k 而非 ℕ，说明 act 为什么值得当参数 -/
def dictator (n k : ℕ) : Mech (act := Fin k) n where
  O := Option (Fin k)
  M := fun v => v.toList.head?

/- 作为结构字段：字段类型已把 act 钉死 -/
structure Auction (n : ℕ) where
  base : Mech (act := ℕ) n
  p : base.O → Fin n → Option ℕ

def myAuction (n : ℕ) : Auction n where
  base := { O := Option (Fin n), M := fun b => Fin.find? fun i => decide (∀ j, b.get j ≤ b.get i) }
  p := fun _ _ => none

/- act 已知的消费函数 -/
def runIt {n : ℕ} (m : Mech (act := ℕ) n) (b : ℕ ^ n) : m.O := m.M b

/- act 通用的消费函数 -/
def outcomeOf {act : Type} {n : ℕ} (m : Mech (act := act) n) (b : act ^ n) : m.O := m.M b

end Imp

/- ========================= 版本 E：act 显式 ========================= -/

namespace Exp

structure Mech (act : Type) (n : ℕ) where
  O : Type
  M : act ^ n → O

structure Prefs {act : Type} {n : ℕ} (m : Mech act n) where
  V : Fin n → act
  U : Fin n → m.O → ℕ

def Truthful {act : Type} {n : ℕ} {m : Mech act n} (p : Prefs m) : Prop :=
  ∀ (b b' : act ^ n) (i : Fin n), p.U i (m.M b') ≤ p.U i (m.M b)

def highestBidder (n : ℕ) : Mech ℕ n where
  O := Option (Fin n)
  M := fun b => Fin.find? fun i => decide (∀ j, b.get j ≤ b.get i)

def dictator (n k : ℕ) : Mech (Fin k) n where
  O := Option (Fin k)
  M := fun v => v.toList.head?

structure Auction (n : ℕ) where
  base : Mech ℕ n
  p : base.O → Fin n → Option ℕ

def myAuction (n : ℕ) : Auction n where
  base := { O := Option (Fin n), M := fun b => Fin.find? fun i => decide (∀ j, b.get j ≤ b.get i) }
  p := fun _ _ => none

def runIt {n : ℕ} (m : Mech ℕ n) (b : ℕ ^ n) : m.O := m.M b

def outcomeOf {act : Type} {n : ℕ} (m : Mech act n) (b : act ^ n) : m.O := m.M b

end Exp

/- ================= 观察一：两边算的是同一个东西 ================= -/

#eval (Imp.highestBidder 3).M #v[7, 12, 9]      -- some 1
#eval (Exp.highestBidder 3).M #v[7, 12, 9]      -- some 1
#eval (Imp.dictator 3 5).M #v[(2 : Fin 5), 4, 1] -- some 2
#eval (Exp.dictator 3 5).M #v[(2 : Fin 5), 4, 1] -- some 2

/- ================= 观察二：无差别的场合 =================

   下面这些位置，两个版本的源码逐字符相同。

   - 结构字面量构造 mech：`myAuction` 里的 `base := { O := ..., M := ... }`
     （字段类型已经确定了 act，所以字面量不需要任何标注）
   - 投影：`m.O`、`m.M`
   - 构造子：两边都是 `{act}` 隐式，见下面的 #check
   - 应用：`runIt (highestBidder n) b`
-/

#check @Imp.Mech.mk    -- {act} → {n} → (O : Type) → (act ^ n → O) → Imp.Mech n
#check @Exp.Mech.mk    -- {act} → {n} → (O : Type) → (act ^ n → O) → Exp.Mech act n
#check @Imp.Mech.O     -- {act} → {n} → Imp.Mech n → Type
#check @Exp.Mech.O     -- {act} → {n} → Exp.Mech act n → Type

example (n : ℕ) (b : ℕ ^ n) := Imp.runIt (Imp.highestBidder n) b
example (n : ℕ) (b : ℕ ^ n) := Exp.runIt (Exp.highestBidder n) b

/- ================= 观察三：有差别的场合 =================

   每次把类型写出来，隐式版多 9 个字符（`(act := ` 和 `)`）：

     隐式                                  显式
     Mech (act := ℕ) n                     Mech ℕ n
     Mech (act := Fin k) n                 Mech (Fin k) n
     Mech (act := act) n                   Mech act n

   上面两个 namespace 里这样的位置各有 5 处。在只含框架 + 性质层的切片上量过，
   隐式版比显式版多 54 个字符 / 6 处。
-/

section TypeAscriptionSites
variable {act : Type} {n : ℕ}
variable (mi : Imp.Mech (act := act) n) (pi : Imp.Prefs mi)
variable (me : Exp.Mech act n)          (pe : Exp.Prefs me)

example : Prop := Imp.Truthful pi
example : Prop := Exp.Truthful pe
end TypeAscriptionSites

/- ================= 观察四：两边都做不到的场合 =================

   下面三个都编不过，而且两个版本失败方式完全一样。取消注释可以复现。

   (1) 想靠定义体里的 `M` 推出 act。两边都报同一条：
         Because this declaration's type has been explicitly provided, all parameter
         types and holes in its header are resolved before its body is processed;
         information from the declaration body cannot be used to infer what these
         values should be

   def bodyI (n : ℕ) : Imp.Mech n   := { O := Bool, M := fun (_ : ℕ ^ n) => true }
   def bodyE (n : ℕ) : Exp.Mech _ n := { O := Bool, M := fun (_ : ℕ ^ n) => true }

   (2) 性质层里最省事的写法——连 m 的类型都不写。两边都报
         Failed to infer type of binder `m`

   theorem bareI {m} (p : Imp.Prefs m) (h : Imp.Truthful p) : Imp.Truthful p := h
   theorem bareE {m} (p : Exp.Prefs m) (h : Exp.Truthful p) : Exp.Truthful p := h

   结论：所谓 "header 先于 body 解析" 的限制对两边一视同仁，那不是显式的优势。
   一个永远推不出来的隐式参数，只是一个更难写的显式参数。
-/

/- ================= 观察五：唯一隐式占优的场合 =================

   纯 term 位置（没有声明类型的 fun / example），elaborator 不分头部和体，
   act 能从体里推出来。此时隐式什么都不用写，显式要写一个 `_`。
   但在以 def / theorem 为主的开发里这种形态很少见。
-/

#check fun {n : ℕ} (m : Imp.Mech n)   (b : ℕ ^ n) => m.M b
#check fun {n : ℕ} (m : Exp.Mech _ n) (b : ℕ ^ n) => m.M b

/- ================= 观察六：显式让未决项可见 =================

   两个 #check 都"成功"，但隐式版打印出的 `Imp.Mech 3` 看起来像个完整类型，
   其实里面藏着一个没解出来的 ?act；显式版把它明摆着显示成 ?m.1。
-/

#check (Imp.Mech (n := 3))   -- Imp.Mech 3 : Type 1
#check (Exp.Mech _ 3)        -- Exp.Mech ?m.1 3 : Type 1
