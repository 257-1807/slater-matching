# Slater 数与极小基数的极大匹配：查重记录

2026 年 11 月 25 日核查。作者语料给出两条欧拉图候选。在下列可检索资料中未找到其完整证明，亦未找到对所有最小度至少 2 的图陈述同一度数列不等式的先行论文。最接近的已发表结果是 Caro 等人 2022 年的定理 3.2，证明已经用到相同的截边双计数。本项目保留了端点的实际度数，所得 Slater 界是该论证的度数列细化。[期刊论文，第 267 页](https://ajc.maths.uq.edu.au/pdf/84/ajc_v84_p258.pdf#page=10)

## 原题与定义

Ján Pastorek 的 *AutoGraphForge: Towards Automated Graph Theory Discovery*（2026，arXiv:2609.03478v1）给出了公开候选语料及其状态说明。按作者仓库 `4d1a8afc99447cacd2328cca20e47b6493e8dbc5` 读取原始排名表。方括号中数字是 touch count。[论文](https://arxiv.org/abs/2609.03478v1) · [原始排名表](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/results/survivors_by_touch.txt)

| 表中排名 | 原始文件行号 | 候选陈述 |
|---:|---:|---|
| 605 | 611 | `(((nontrivial) ∧ (K_4_free)) ∧ (eulerian)) ⇒ slater ≤ min_maximal_matching_number` |
| 597 | 603 | `(((nontrivial) ∧ (eulerian)) ∧ (planar)) ⇒ slater ≤ min_maximal_matching_number` |

- 作者形式化将 `nontrivial` 定义为顶点数至少 2，`eulerian` 表示连通且所有度数为偶数。作者库的 `slaterNumber` 为最小的 $s$，使 $s$ 加上降序排列的前 $s$ 项度数之和至少为顶点数。因此在非空有限图上与 Gentner、Rautenbach 陈述的 Slater 数一致。[作者定义](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/lean_project/LeanProject/GraphInvariants.lean) · [Gentner–Rautenbach](https://arxiv.org/pdf/1608.04560#page=2)
- GraphCalc 的同名不变量是所有包含意义下极大的匹配中最小的基数。文献中也称边支配数 $\gamma_e$，或 saturation number。Baste、Fürst、Henning、Mohr 和 Rautenbach 采用这个等价定义。注意本项目的度数列下界研究的是 minimum maximal matching，与 maximum matching 的问题不同。[GraphCalc 源码及说明](https://graphcalc.readthedocs.io/en/stable/_modules/graphcalc/graphs/invariants/domination.html#min_maximal_matching_number) · [Baste 等，第 2 页](https://arxiv.org/pdf/1905.12241#page=2)

## 与已知结果的数学关系

Yair Caro、Randy Davila、Michael A. Henning、Ryan Pepper 的 *Conjectures of TxGraffiti: Independence, domination, and matchings*（Australas. J. Combin. 84(2), 2022, 258–274）定理 3.2 给出 $\gamma_e(G)\ge\delta n/[2(\Delta+\delta-1)]$。他们取最小基数的极大匹配 $M$，用 $A$ 表示覆盖到的顶点，$B$ 表示其余顶点。$B$ 独立，且每个 $A$ 顶点至少有一条邻边留在 $A$ 内，因此 $\delta|B|\le e(A,B)\le(\Delta-1)|A|$。[原定理及证明](https://ajc.maths.uq.edu.au/pdf/84/ajc_v84_p258.pdf#page=10)

在同一证明中保留各端点实际度数，得到 $\sum_{v\in A}d(v)\ge\delta|B|+2|M|$。当 $\delta\ge2$，该和至少为 $2(n-|M|)$，全图最大的 $|M|$ 项度数之和至少为此和的一半。这个细化给出 $\mathrm{sl}(G)\le |M|$。取三个三角形共中心的七点友谊图，再把一个度 2 顶点与八圈的一个顶点识别，得到同时属于两个候选图类的 14 点图。其度序列为 $6,4,2,\ldots,2$，Slater 数为 3，而定理 3.2 的数值下界为 2。因此已发表的定理本身只给出部分所需的数值信息。

Bahadır 的 *On Total Domination and Minimum Maximal Matchings in Graphs* 讨论的是全支配数与匹配。Baste 等还给出不少匹配上界；其论文没有陈述此 Slater 不等式。关于支配数与边支配数的特殊图类结果，在对应图类内可能推出 Slater 界；例如仅对正则图的结果无法覆盖这里允许的不规则欧拉图。[Bahadır](https://arxiv.org/abs/1907.11590) · [Baste 等](https://arxiv.org/abs/1905.12241) · [正则图的相关研究](https://arxiv.org/abs/2608.22498)

## 检索记录

| 渠道 | 查询与结果 |
|---|---|
| OpenAlex 关键词与引文链 | 原论文 W7208712928 的反向引文为 0。全文查询 `"Slater number" "minimum maximal matching"` 仅返回原论文，而与 `"edge domination"` 或 `"saturation number"` 搭配的查询均返回 0。查询 `AutoGraphForge` 的五条结果中，另四条分别涉及燃烧数与 Slater 数、Roman/双 Roman 支配或 power domination。Caro 等人的 arXiv 记录 W3146316572 有 1 条索引引文，涉及零迫数与顶点覆盖；Gentner–Rautenbach W2515296793 有 8 条索引引文，逐项审阅题名未见此结论。[AutoGraphForge 全文检索](https://api.openalex.org/works?search=AutoGraphForge&per_page=100) · [Caro 等引文](https://api.openalex.org/works?filter=cites:W3146316572) · [Slater 论文引文](https://api.openalex.org/works?filter=cites:W2515296793) |
| arXiv、Semantic Scholar | arXiv 的 all-fields 查询 `"Slater number" "minimum maximal matching"`、`"Slater number" "edge domination"` 都未列出条目。Semantic Scholar 原论文前向引文返回空；其 bulk 查询 `"Slater number" + "maximal matching"` 返回 0。[arXiv](https://arxiv.org/search/?searchtype=all&query=%22Slater+number%22+%22minimum+maximal+matching%22) · [Semantic Scholar 引文](https://api.semanticscholar.org/graph/v1/paper/ARXIV:2609.03478/citations?fields=title,externalIds&limit=100) |
| Google Scholar | 精确词组 `"Slater number" "minimum maximal matching"` 与 `"edge domination number" "degree sequence" graph` 的直接 HTTP 请求均遇到验证页。随后在桌面浏览器中检索。`"Slater number" "maximal matching"` 得两条结果，分别为 Haynes、Hedetniemi、Henning 的 2023 年专章 *Domination in Trees* 和 Pastorek 原论文；前者仅核查到出版方的摘要与搜索摘录。`"AutoGraphForge" "d7f95ad0"` 提示没有匹配文章。[专章](https://doi.org/10.1007/978-3-031-09496-5_5) · [两结果查询](https://scholar.google.com/scholar?q=%22Slater+number%22+%22maximal+matching%22) · [条目查询](https://scholar.google.com/scholar?q=%22AutoGraphForge%22+%22d7f95ad0%22) · [直接查询入口](https://scholar.google.com/scholar?q=%22Slater+number%22+%22minimum+maximal+matching%22) |
| Figshare、DataCite、Zenodo | Figshare 原生 POST 检索 `"Slater number" "maximal matching"` 和 `"Slater" "edge domination"` 均返回空，单查 `"Slater number"` 返回先前的燃烧问题及其软件。DataCite 的 `"Slater number" AND "matching"` 返回 0，`AutoGraphForge` 返回 5 条 DOI，含重复版本，无本题解答。Zenodo 直接 API 返回 403；通过 OpenAlex、DataCite 的 Zenodo DOI 元数据和站点关键词交叉检索，找到的 AutoGraphForge Zenodo 树反例为其他命题。[Figshare 搜索端点](https://api.figshare.com/v2/articles/search) · [DataCite](https://api.datacite.org/dois?query=AutoGraphForge) |
| GitHub | Issues/PR 搜索 `"AutoGraphForge" "Slater" "matching"` 及 `repo:JanPastorek/AutoGraphForge "Slater"` 均无结果。`"Slater number" "edge domination"` 命中一条图不变量单元测试 PR。`"Slater number" "maximal matching" in:readme` 仅找到提供两种图参数的 grinpy。匿名 API 返回 401，已另通过有身份验证的 GitHub 全站代码搜索检查两个编号与 `slater` 的组合、`slaterNumber minMaximalMatching` 及不等式原文，未找到完整证明。逐项检查上游发布的反例表、验证目录和 13 个候选挑战；作者公开议题 #1 处理另一个色数候选。[公开 issues 查询](https://api.github.com/search/issues?q=%22AutoGraphForge%22%20%22Slater%22%20%22matching%22) · [grinpy](https://github.com/somacdivad/grinpy) |
| MathOverflow、Lean 社区与 Mathlib | MathOverflow API 的 `Slater number maximal matching` 返回空，普通搜索的相关结果仅涉及最大匹配等其他问题。Lean 公开 Zulip 归档与 GitHub 的定域关键词检索未找到此定理；本机 Mathlib 快照 `fc4f59e5` 中以 `slater(number\| number)\|minimum maximal matching\|edge domination number` 搜索无直接命中。术语检索可能漏掉以其他符号叙述的同义结果。[MathOverflow 查询](https://api.stackexchange.com/2.3/search/advanced?site=mathoverflow&q=Slater%20number%20maximal%20matching) · [Lean 社区公开归档](https://leanprover-community.github.io/archive/) |

普通网页检索另外使用 `sub-domination number / subdomination number`、`minimum size of a maximal matching`、`degree sequence`、`degree sum`、`sum of largest degrees`、`minimum degree two`、`maximal matching lower bound`、`Eulerian`、`K4-free` 等组合。以上结果支持作者将该语料行列为有待证明，无法排除不同记号、非公开文稿或未收录论文中的同义论证。
