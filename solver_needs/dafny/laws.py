"""The ten sequence laws of the AX probe for Dafny.

Each law is a Boogie axiom in the form Dafny's own prelude uses for its
sequence axioms. The probe appends one law to the prelude of the Dafny in
use and verifies the stripped program with that prelude; laws are never
combined, because together they cause matching loops.
"""

from pathlib import Path

from solver_needs import config

LAWS: dict[str, str] = {
    "take-take": """
axiom (forall l: Seq, n: int, m: int ::
  { Seq#Take(Seq#Take(l, m), n) }
  0 <= n && n <= m && m <= Seq#Length(l)
     ==> Seq#Take(Seq#Take(l, m), n) == Seq#Take(l, n));
""",
    "take-append": """
axiom (forall s: Seq, t: Seq, n: int ::
  { Seq#Take(Seq#Append(s, t), n) }
  (0 <= n && n <= Seq#Length(s)
     ==> Seq#Take(Seq#Append(s, t), n) == Seq#Take(s, n)) &&
  (Seq#Length(s) < n && n <= Seq#Length(s) + Seq#Length(t)
     ==> Seq#Take(Seq#Append(s, t), n) == Seq#Append(s, Seq#Take(t, n - Seq#Length(s)))));
""",
    "take-full": """
axiom (forall s: Seq ::
  { Seq#Take(s, Seq#Length(s)) }
  Seq#Take(s, Seq#Length(s)) == s);
""",
    "append-empty": """
axiom (forall s: Seq :: { Seq#Append(s, Seq#Empty()) } Seq#Append(s, Seq#Empty()) == s);
axiom (forall s: Seq :: { Seq#Append(Seq#Empty(), s) } Seq#Append(Seq#Empty(), s) == s);
""",
    "take-build": """
axiom (forall s: Seq, n: int ::
  { Seq#Append(Seq#Take(s, n), Seq#Build(Seq#Empty(), Seq#Index(s, n))) }
  { Seq#Take(s, n), Seq#Index(s, n) }
  0 <= n && n < Seq#Length(s)
     ==> Seq#Append(Seq#Take(s, n), Seq#Build(Seq#Empty(), Seq#Index(s, n))) == Seq#Take(s, n + 1));
""",
    "split-concat": """
axiom (forall s: Seq, n: int ::
  { Seq#Append(Seq#Take(s, n), Seq#Drop(s, n)) }
  0 <= n && n <= Seq#Length(s)
     ==> Seq#Append(Seq#Take(s, n), Seq#Drop(s, n)) == s);
""",
    "append-assoc": """
axiom (forall a: Seq, b: Seq, c: Seq ::
  { Seq#Append(Seq#Append(a, b), c) } { Seq#Append(a, Seq#Append(b, c)) }
  Seq#Append(Seq#Append(a, b), c) == Seq#Append(a, Seq#Append(b, c)));
""",
    "drop-append": """
axiom (forall s: Seq, t: Seq, n: int ::
  { Seq#Drop(Seq#Append(s, t), n) }
  (0 <= n && n <= Seq#Length(s)
     ==> Seq#Drop(Seq#Append(s, t), n) == Seq#Append(Seq#Drop(s, n), t)) &&
  (Seq#Length(s) < n && n <= Seq#Length(s) + Seq#Length(t)
     ==> Seq#Drop(Seq#Append(s, t), n) == Seq#Drop(t, n - Seq#Length(s))));
""",
    "drop-build": """
axiom (forall s: Seq, n: int ::
  { Seq#Append(Seq#Build(Seq#Empty(), Seq#Index(s, n)), Seq#Drop(s, n + 1)) }
  { Seq#Drop(s, n), Seq#Index(s, n) }
  0 <= n && n < Seq#Length(s)
     ==> Seq#Append(Seq#Build(Seq#Empty(), Seq#Index(s, n)), Seq#Drop(s, n + 1)) == Seq#Drop(s, n));
""",
    "drop-full": """
axiom (forall s: Seq :: { Seq#Drop(s, 0) } Seq#Drop(s, 0) == s);
axiom (forall s: Seq :: { Seq#Drop(s, Seq#Length(s)) } Seq#Drop(s, Seq#Length(s)) == Seq#Empty());
axiom (forall s: Seq :: { Seq#Take(s, 0) } Seq#Take(s, 0) == Seq#Empty());
""",
}


def write_preludes(out_dir: Path | None = None) -> dict[str, Path]:
    """Write one extended prelude per law and return ``{law: path}``.

    The base is the prelude shipped next to the Dafny in use
    (``config.dafny_prelude()``); the files go to ``work/preludes/`` by default.
    """
    out_dir = out_dir or config.WORK / "preludes"
    base = config.dafny_prelude().read_text()
    out_dir.mkdir(parents=True, exist_ok=True)
    paths: dict[str, Path] = {}
    for name, axiom in LAWS.items():
        path = out_dir / f"{name}.bpl"
        path.write_text(base + f"\n// --- sequence law: {name} ---\n" + axiom)
        paths[name] = path
    return paths
