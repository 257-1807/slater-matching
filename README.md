# 用度数列估计极大匹配的边数

**定理。** 若有限无向简单图 $G$ 的每个顶点都至少有两个邻点，则每个极大匹配的边数都至少为 $G$ 的 Slater 数。因此

$$
\operatorname{sl}(G)\leq\mu^*(G),
$$

其中 $\mu^*(G)$ 是所有极大匹配中最小的边数。这个结论解决了 Ján Pastorek 的 AutoGraphForge 公开候选 `d7f95ad0`。四顶点路径 $P_4$ 说明，将最小度条件放宽到 1 后结论就会失效。原猜想、推广与这个边界反例都已通过 Lean 4.36.0 验证。[主定理](SlaterMatching/Bound.lean) · [四顶点路径](SlaterMatching/Sharpness.lean) · [公理日志](audit/axioms.log)

## 公开问题的来源

Ján Pastorek，*AutoGraphForge: Towards Automated Graph Theory Discovery*，2026，arXiv:2609.03478。作者在“Code availability”中给出了结果仓库。候选的稳定 ID 是 `d7f95ad0`，在固定快照的原始表中排第 605，位于第 611 行。作者的结果 JSON 把它记为 `proposed`，所附的 Lean 陈述与证明字段均为空。[原论文](https://arxiv.org/abs/2609.03478v1) · [论文中的代码来源](https://arxiv.org/html/2609.03478v1) · [原始表第 611 行](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch.txt#L611)

原始 `statement` 字段逐字为

```text
(((nontrivial) ∧ (K_4_free)) ∧ (eulerian)) ⇒ slater ≤ min_maximal_matching_number
```

即：至少有两个顶点、没有四顶点团的欧拉图满足上述不等式。作者把欧拉图定义为连通且每个顶点的度数均为偶数的图。这样的图中每个顶点都有邻点，正偶数度必然至少为 2。这也是推广能覆盖原题的原因。同一语料中的平面欧拉图条目 `4b6081e7` 也直接满足推广的假设。[两个编号及原始状态](audit/source.json) · [作者的图类定义](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/lean_project/LeanProject/GraphInvariantsComputable.lean#L295)

## 证明

设图有 $n$ 个顶点，把度数从大到小排列为 $d_1,\ldots,d_n$，记 $D_k=d_1+\cdots+d_k$，$D_0=0$。Slater 数是使 $k+D_k\ge n$ 成立的最小非负整数 $k$。一个匹配称为**极大**，是指已经无法再添加一条与现有匹配顶点不相交的边。任取这样的匹配 $M$，写 $k=|M|$。要证明的就是 $k+D_k\ge n$。

令 $S$ 为匹配边的所有端点，$U$ 为其余顶点。匹配的边两两没有公共端点，所以 $|S|=2k$。如果 $U$ 中有一条边，就能把它加入 $M$，这与极大性矛盾。因此 $U$ 中每个顶点的邻点都在 $S$。最小度至少为 2，故 $S$ 与 $U$ 之间至少有 $2|U|$ 条边。

对 $S$ 的顶点求度数和时，每条跨边贡献 1。此外，每个 $S$ 中顶点都与自己的匹配伙伴相邻，所以内部邻接至少再贡献 $2k$。于是

$$
\sum_{v\in S}d(v)\ \ge\ 2|U|+2k
=2(n-2k)+2k=2(n-k).
$$

把 $S$ 任意分成两个各含 $k$ 个顶点的集合。每一半的度数和至多是全图最大的 $k$ 项之和 $D_k$。因此 $2D_k\ge2(n-k)$，即 $k+D_k\ge n$。这对每个极大匹配都成立，取边数最小的极大匹配即得定理。

**与已发表证明的关系。** Caro、Davila、Henning 和 Pepper 在 2022 年定理 3.2 的证明中已按匹配端点与未匹配顶点双计数，用最大度 $\Delta$ 和最小度 $\delta$ 得到 $\mu^*(G)\ge\delta n/[2(\Delta+\delta-1)]$。本证明沿用他们的划分，保留端点的实际度数，再用 $D_k$ 控制两个半集。查重报告给出一个 14 点图，原定理的数值下界为 2，Slater 下界为 3。[期刊原文，第 267 页](https://ajc.maths.uq.edu.au/pdf/84/ajc_v84_p258.pdf#page=10) · [先例核对与算例](audit/search.md)

**边界检查。** 四顶点路径的度数是 $2,2,1,1$。单取一个顶点时 $1+2<4$，取两个时 $2+2+2\ge4$，故 Slater 数为 2。中间一条边已构成极大匹配，空匹配尚可加边，故 $\mu^*(P_4)=1$。三角形则给出原图类内的取等实例，两项均为 1。推广按“每个顶点度至少为 2”表述，无需预设连通性；其中空图的两个参数均为 0。原题的 $n\ge2$ 明确排除了零顶点及单顶点的情形。

## 忠实性对照

| 来源的数学含义 | Lean 对应 | 核对方式 |
|---|---|---|
| 任意有限无向简单图 | `[Fintype V]`、`G : SimpleGraph V` | 没有固定顶点数上限。有限图上邻接可判定；证明支持任意这样的实例。 |
| 非平凡、无四团、欧拉 | `2 ≤ Fintype.card V`、`G.CliqueFree 4`、`G.Connected ∧ ∀ v, G.degree v % 2 = 0` | 主定理保留全部源条件。证明中用连通性与偶度推出最小度至少 2。 |
| 降序排列的前 $k$ 项度数之和 | `largestDegreeSum G k` | 在所有大小为 $k$ 的顶点子集上取度数和的最大值。取 $k=n$ 一定达到 Slater 门槛。 |
| 最小的 $k$ 使 $k+D_k\ge n$ | `slaterNumber G`、`slater_spec` | 在自然数中取下确界并证明它达到门槛。 |
| 包含意义下极大的匹配 | `Maximal (fun N : G.Subgraph => N.IsMatching) M` | Mathlib 的匹配子图中，每个被覆盖顶点恰有一个匹配邻点。项目证明了极大性等价于匹配端点覆盖每条边。 |
| 边数最小的极大匹配 | `minMaximalMatchingNumber G`、`exists_minimum_matching` | 用 `Nat.card M.edgeSet` 计无向边；证明极大匹配存在且最小值可达。 |
| 原命题与推广 | `conjecture_d7f95ad0`、`slater_le_minMaximalMatching` | 前者保留原假设，后者量化所有最小度至少为 2 的有限简单图。 |

## 查重与候选筛选

**查重日期为 2026-11-25。** 使用编号 `d7f95ad0`、`Slater number`、`minimum maximal matching`、`edge domination number`、`saturation number` 及度数列相关词组，核对了作者源数据、arXiv、Google Scholar、前向引文、GitHub 全站代码与议题、MathOverflow、Lean Zulip、Mathlib 及数据存档。Google Scholar 的精确词组 `"Slater number" "maximal matching"` 返回原论文与一本讨论树的专章。已核查来源中未发现本题或上述推广的完整先行证明；检索结果不能确立全球首证优先权。[逐平台检索记录、来源与限制](audit/search.md)

| 本轮候选 | 可攻克性、形式化成本及取舍 |
|---|---|
| Golfieri、Schvöllner，*On the Δ-primitive squares conjecture*（2026，arXiv:2611.11574），猜想 3.18 | 单个 Pell 数的反例可以用整数等式验证，全称唯一性还需处理无界因子，留作备选。[原文 §3](https://arxiv.org/html/2611.11574v1#S3) |
| Coulter、Do，*From Weingarten calculus for real Grassmannians to deformations of monotone Hurwitz numbers and Jucys–Murphy elements*（2025，arXiv:2506.04002），猜想 4.21 | 递推可生成多项式，再查是否全实根；有限筛查未找到反例，对所有分拆的证明成本较高。[原文 §4](https://arxiv.org/html/2506.04002v1#S4.SS3) |
| Pastorek，*AutoGraphForge*（2026，arXiv:2609.03478），`fe71fb58` | 关于燃烧数与 Slater 数的界可用有限图检验。查到 Seth Christopher 2026 年 9 月发布的 15 点反例与无界族后排除。[已有反例](https://doi.org/10.6084/m9.figshare.33476293.v1) |
| 同一语料，`f0a6258d` | 色数与平均度不等式便于精确检验。作者仓库的公开议题已给出 $K_{19}$ 反例，排除。[已有反例](https://github.com/JanPastorek/AutoGraphForge/issues/1) |
| 同一语料，`d7f95ad0` | 选定。极大匹配可用 Mathlib 的子图表示，证明全程使用有限集、顶点度数与整数比较。[原始陈述](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch.txt#L611) |

## 复现与审计

安装 Elan，在项目根目录执行以下命令。项目固定 Lean 4.36.0 及 Mathlib v4.36.0；具体依赖提交保存在 `lake-manifest.json`。[Elan 安装说明](https://github.com/leanprover/elan)

```sh
lake exe cache get Mathlib.Tactic Mathlib.Combinatorics.SimpleGraph.Matching Mathlib.Combinatorics.SimpleGraph.DegreeSum Mathlib.Combinatorics.SimpleGraph.Hasse Mathlib.Combinatorics.Enumerative.DoubleCounting Mathlib.Order.Preorder.Finite
lake build
lake --wfail build
lake env lean -DwarningAsError=true SlaterMatching.lean
for m in Slater Matching Counting Bound Sharpness; do
  lake env leanchecker --verbose "SlaterMatching.$m" || exit 1
done
python3 scripts/check_graphs.py
```

独立 Python 枚举检查了 2 至 6 个顶点的全部 **12,332** 张最小度至少为 2 的带标号简单图，允许不连通。它枚举可行匹配，并检查未匹配顶点构成独立集。上面的数学证明和 Lean 主定理覆盖任意有限阶数。[程序](scripts/check_graphs.py) · [枚举输出](audit/examples.log)

根文件末尾的 `#print axioms` 给出了主定理的实际输出。严格构建零报错、零警告，源码没有 `sorry`、`admit` 或自定义公理，含证明的模块均已逐个内核重放。[严格构建日志](audit/build.log) · [完整公理输出](audit/axioms.log) · [内核重放日志](audit/kernel-replay.log)

```text
'SlaterMatching.conjecture_d7f95ad0' depends on axioms: [propext, Classical.choice, Quot.sound]
```

本项目的原创代码和说明采用 Apache-2.0 许可证，原题和引述保留其来源。[许可证](LICENSE)
