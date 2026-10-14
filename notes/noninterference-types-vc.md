# 用 dot/fiber 把 noninterference 落到结果类型与函数契约

这里沿用 `ContextLogic/examples/HypraSecure.v` 的 **同一个整数程序**，包括负数和两个原始条件分支。
基础是 `negation` 聊天附件 *Fiber-Guided Support Refinement and Type Negation* 第 1–2 节；不使用其中尚待证明的 type-negation 翻译。

## 1. dot 的位置：观察低输入，不固定秘密

文档的 qualifier-dot 是 support padding：

\[
  X.\{\phi\}=(X\cup FV(\phi),\ \sigma\mapsto
     \phi(\sigma\upharpoonright_{FV(\phi)})).
\]

`ContextQualifier/theories/SupportPadding.v` 中的 `qual_pad` 实现这个操作：扩大 support，谓词只读取原 support 的投影。
已证明 support 公式、空 padding 恒等式和 top 的 padding 公式。
特别是 `{l}.{top}` 保留 `l` 的观察信息，不能被化简成空 support 的 top。

但是，论文记号下的 $\{\nu:\mathsf{int}\mid\{l\}.\{\top\}\}$ **不能独自表达 noninterference**：
它仍允许同一个 `l` 对应多个输出。dot 负责指定按什么分 fiber；Low 负责要求每个 fiber 内输出一致。

实现中的语义结果类型原型为：

```text
tau ::= Bound | Low | Observe(X, tau)
```

其解释是：

\[
\begin{aligned}
\llbracket Bound\rrbracket_o&=FBound(o),\\
\llbracket Low\rrbracket_o&=FLow(o),\\
\llbracket Observe(X,\tau)\rrbracket_o
  &=FFibVars(X,\llbracket\tau\rrbracket_o).
\end{aligned}
\]

`Observe` 是本次明确增加的**整个结果类型的 fiber 包装**，不是声称原文已经给出 `X.tau` 的语法。
文档原有 dot 仅作用于 qualifier；把它直接写到 `square tau` 外面需要这一额外解释。
代码中的 `padded_low_result_ty l` 先用真实的 `qual_pad {l} top` 获得观察域，再包装 Low。

核心结果类型是：

\[
  NIResult(l) := Observe(\{l\},Low).
\]

`padded_low_result_eq` 和 `ni_result_denote` 证明它的解释恰好就是原来的 `FNoninterference l o`。
`ni_result_spec` 进一步给出同低输入、同输出的两执行刻画，不另加新逻辑连接词。

`low_result_persistence` 还证明：

\[
  FLow(o)\quad\Longleftrightarrow\quad FPersist(FBound(o)).
\]

因此 Low 使用的是现有 persistence 的取值一致性含义。与原 context-type 语法对应时，
候选是 $\Box\{\nu:b\mid\top\}$ 加上基本类型约束；不能省略外层按低输入划分 fiber 的步骤。
`ContextTyping/theories/LowContextType.v` 定义了这个真实的 `context_ty`，并证明
已有基本结果 denotation 加上 Low 能推出该 persistent 类型的 denotation。
这个引入桥接不等于原整数程序已经获得 `has_context_type` 推导。

## 2. 函数类型：两种等价的语义接口

`has_fiber_function_type pre tau out run` 要求：对所有满足输入类型的 capability，完整输出像都满足结果类型。
这里量化的是环境集合，`run` 不是任意挑选的一次执行。

对于 `f : Z -> Z -> Z`（参数顺序为 high、low），实现了两个接口：

```text
NI function:
  (Bound(h), Bound(l)) -> Observe({l}, Low(o))

Low-preserving function:
  (Bound(h), Low(l)) -> Low(o)
```

前者允许一个 capability 同时包含不同的低输入；后者只要求在低输入一致的 capability 上保持输出一致。
`ni_function_type_iff` 与 `low_function_type_iff` 分别证明它们都等价于：

\[
  \forall h_1,h_2,l\in\mathbb Z.\ f(h_1,l)=f(h_2,l).
\]

逆向证明显式构造包含 `(h1,l)`、`(h2,l)` 的双环境 capability，所以这些接口不会仅仅在某个特殊输入集合上成立。
不要求输入的 high/low 为笛卡尔积：定理对任意已绑定输入 capability 成立。

对当前全定义、确定性的函数片段，还证明：

\[
  f:NI\quad\Longleftrightarrow\quad
  \exists g:\mathbb Z\to\mathbb Z.\ \forall h,l.\ f(h,l)=g(l).
\]

这给出普通数值 refinement 的可选接口：结果由只读取低输入的 summary `g` 描述。
`secure` 可取 `g(l)=2*l`。一般 NI 类型不应预先写死 `2*l`，否则会把一个 hyperproperty 加强成该程序的完整函数规格。
该等价只在此处的全定义确定性片段证明，不能直接推广到非确定性程序。

## 3. 使用原 context-logic 例子检查表达是否合适

原程序为：

```text
o := if h > 0 then 2*l else l;
if h <= 0 then o+l else o
```

`HypraSecureTyping.v` 中的已检验性质：

| 例子/规格 | 结果 | 说明 |
|---|---|---|
| 原 `secure` 的 NI 函数类型 | 接受 | 固定 l，所有秘密输入都返回 2*l |
| 原 `secure` 的 Low-preserving 类型 | 接受 | 输入 l 一致则输出一致 |
| 原 `first_if` 的 NI 函数类型 | 拒绝 | h=1 与 h=-1、l=3，分别返回 6 和 3 |
| 常数函数的 NI 类型 | 接受 | NI 不要求输出覆盖所有整数 |
| 原 `secure` 对所有输入集合返回全局 Low | 拒绝 | l=0 与 l=1 产生不同输出，本应允许 |

不能把 `{l}` 随意扩大成 `{h,l}`：固定所有输入后，确定性泄漏函数 `f(h,l)=h` 也会在每个输入 fiber 内输出一致，因而弱化了目标安全性质。
这里 dot 的 support 是安全策略的一部分，而不是“越大越强”的装饰。

## 4. VC：共享低输入、独立秘密、允许不同分支

`HypraSecureVC.v` 的 `vcgen` 对一份有限路径摘要枚举所有路径配对。
每个路径含算术 guard 和结果表达式。配对 VC 为：

\[
\forall h_1,h_2,l.\quad
 G_i(h_1,l)\land G_j(h_2,l)
 \Longrightarrow E_i(h_1,l)=E_j(h_2,l).
\]

这正是 dot/fiber 的操作性解释：两边共享 `l`，但不约束 `h1=h2`，也不要求路径相同。
等价地，可使用两份低输入并在前提加入 `l1=l2`。

原 `secure` 的两个条件产生以下四条符号路径：

| 第一分支 h>0 | 第二分支 h<=0 | Guard | 结果 |
|---|---|---|---|
| true | true | h>0 且 h<=0 | 3*l，不可达 |
| true | false | h>0 | 2*l |
| false | true | h<=0 | l+l |
| false | false | h<=0 且 h>0 | l，不可达 |

`vcgen` 产生 16 个路径对，含不可达路径的 12 个 VC 由 guard 矛盾成立；其余四个都已证明。
例如，两个可达的不同分支对应关键 VC：

\[
  h_1>0\land h_2\le0\Longrightarrow 2l=l+l.
\]

只有第一个 if 的程序则产生失败 VC：

\[
  h_1>0\land h_2\le0\Longrightarrow 2l=l,
\]

其中 `(h1,h2,l)=(1,-1,3)` 是原逻辑例子中的反例。
因此不能只逐个分支检查 high 是否在结果表达式中出现：单分支表达式均不提 high，跨分支却可能泄漏。

`vcgen_correct` 证明：**若路径摘要对程序语义 sound 且覆盖所有输入，VC 全部成立当且仅当上述 NI 函数类型成立。**
两个程序都给出了已检查的路径 soundness/coverage 证明，`secure_typed_via_vcs` 从 VC 推出函数类型。
`secure` 的路径 soundness 直接展开原来的两个 if；不以预先证明的 `secure_result` 当作 VC。

## 5. 实现边界与复现

这是一个有 Rocq 证明的**语义类型与路径 VC 原型**：

- 已实现 qualifier-dot、整个结果类型的 fiber 包装及它们之间的连接。
- 已证明原 context-logic NI 性质与函数类型的双向对应，并复用原程序和反例。
- 已证明有限精确路径摘要下的 VC 正确性；当前用 `lia` 验证整数线性算术。
- `vcgen` 消费带 soundness/coverage 证明的路径摘要；尚无通用源码到路径摘要的编译器。
- 没有扩充现有 `context_ty`、`has_context_type` 或原 Fundamental 定理，也没有把整数程序偷偷改成自然数程序。
- 将该原型纳入原 CoreLang 的语法类型检查，需要明确增加类型层观察构造，或证明可编码性；原程序还需要整数及算术语言支持。
- 这里的 Low 是输出取值一致性，不是 Under coverage；不使用 type-negation 翻译来代替 NI。

复现：

```sh
rocq makefile -f _CoqProject -o Makefile
timeout 50s make -j2 ContextTyping/examples/HypraSecureVC.vo ContextTyping/theories/LowContextType.vo
```

关键文件：`ContextQualifier/theories/SupportPadding.v`、`ContextTyping/theories/FiberResult.v`、
`ContextTyping/examples/HypraSecureTyping.v`、`ContextTyping/examples/HypraSecureVC.v`。

2026-10-14 在本机 Rocq 9.0.0 下完成上述两个目标及其依赖的编译。
新增文件没有 `Admitted` 或新公理；对 `vcgen_correct` 和 `secure_typed_via_vcs` 的
`Print Assumptions` 检查仅列出原有基础库使用的命题外延性、函数外延性与证明无关性。
