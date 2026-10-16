# Program corpora

The four program corpora, exactly the files the extractors read.

| Directory | Corpus | Files | Origin | Licence | How obtained | What was changed |
|---|---|---|---|---|---|---|
| `CF-D/` | Codeforces-Dafny (CF-D) | 108 `.dfy` | [Codeforces](https://codeforces.com) problems (difficulty 800–1600) and user solutions, taken from the Hugging Face datasets [open-r1/codeforces](https://huggingface.co/datasets/open-r1/codeforces) (problem statements) and [open-r1/codeforces-submissions](https://huggingface.co/datasets/open-r1/codeforces-submissions) (user solutions) | CC BY 4.0 (`LICENSE-DATA` at the repository root, with the attribution chain) | Each program was produced by an LLM agent from one problem statement together with one user's Python solution: a method body with a formal contract, annotated with invariants, assertions, ghost variables and helper lemmas until it verified | Generated programs; the problem statements and Python solutions are not included |
| `DB/` | DafnyBench (DB) | 785 `.dfy` | The `ground_truth` programs of [DafnyBench](https://github.com/sun-wendy/DafnyBench) at commit `0cd28feed9cd0179b07fdb9d002f8c39063658e4`; the programs were collected from GitHub by the DafnyBench authors | Apache License 2.0 (`DB/LICENSE`, upstream) | Copied verbatim | Renamed: `DB_` plus the original stem with characters outside `[A-Za-z0-9_.-]` replaced by `_`; `DB/MANIFEST.json` maps each file to its original name |
| `CF-V/` | Codeforces-Verus (CF-V) | 94 `.rs` | The CF-D programs of the same name | CC BY 4.0 (`LICENSE-DATA`) | Each program was translated from its CF-D program by an LLM agent and annotated until it verified | Generated programs |
| `VB/` | Verus-Bench (VB) | 154 `.rs` | The `verified/` solutions of the four Verus-Bench suites (CloverBench, Diffy, MBPP, Misc) in [microsoft/verus-proof-synthesis](https://github.com/microsoft/verus-proof-synthesis), `benchmarks/Verus-Bench` at commit `cbf9c0c6337b224fd8e5b7cb4e01ae65c0f98bc1` | MIT (`VB/LICENSE`, upstream) | Copied verbatim | Only the `verified/` solutions are kept, as `<suite>/<name>.rs`; the `unverified/` inputs are not |

A CF-D or CF-V program's name is `<index>_<contest>_<problem>`: `0012_1060_A`
is Codeforces problem 1060/A.

A program's name in the datasets (`problem`) is its file stem (`0012_1060_A`,
`DB_Clover_only_once`) or, for VB, `<suite>/<stem>` (`MBPP/task_id_3`).

## Citing the third-party corpora

- DafnyBench: Chloe Loughridge, Qinyi Sun, Seth Ahrenbach, Federico Cassano,
  Chuyue Sun, Ying Sheng, Anish Mudide, Md Rakib Hossain Misu, Nada Amin and
  Max Tegmark. *DafnyBench: A Benchmark for Formal Software Verification.*
  arXiv:2406.08467, 2024.
- Verus-Bench (AutoVerus): Chenyuan Yang, Xuheng Li, Md Rakib Hossain Misu,
  Jianan Yao, Weidong Cui, Yeyun Gong, Chris Hawblitzel, Shuvendu Lahiri,
  Jacob R. Lorch, Shuai Lu, Fan Yang, Ziqiao Zhou and Shan Lu. *AutoVerus:
  Automated Proof Generation for Rust Code.* arXiv:2409.13082, 2024.
