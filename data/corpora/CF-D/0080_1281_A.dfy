ghost predicate EndsWith(s: string, suffix: string)
{
  |s| >= |suffix| && s[|s| - |suffix|..] == suffix
}

ghost predicate ValidSentence(s: string)
{
  EndsWith(s, "po") || EndsWith(s, "desu") || EndsWith(s, "masu") || EndsWith(s, "mnida")
}

ghost function ClassifySentence(s: string): string
  requires ValidSentence(s)
{
  if EndsWith(s, "po") then "FILIPINO"
  else if EndsWith(s, "desu") || EndsWith(s, "masu") then "JAPANESE"
  else "KOREAN"
}

ghost function ClassifyAll(sentences: seq<string>): seq<string>
  requires forall i :: 0 <= i < |sentences| ==> ValidSentence(sentences[i])
  decreases |sentences|
{
  if |sentences| == 0 then []
  else ClassifyAll(sentences[..|sentences|-1]) + [ClassifySentence(sentences[|sentences|-1])]
}

lemma ClassifyAllAppend(sentences: seq<string>)
  requires |sentences| > 0
  requires forall i :: 0 <= i < |sentences| ==> ValidSentence(sentences[i])
  ensures ClassifyAll(sentences) == ClassifyAll(sentences[..|sentences|-1]) + [ClassifySentence(sentences[|sentences|-1])]
{
}

lemma LastCharDeterminesClassification(s: string)
  requires ValidSentence(s)
  requires |s| >= 1
  ensures s[|s| - 1] == 'o' ==> EndsWith(s, "po")
  ensures s[|s| - 1] == 'u' ==> (EndsWith(s, "desu") || EndsWith(s, "masu"))
  ensures s[|s| - 1] != 'o' && s[|s| - 1] != 'u' ==> EndsWith(s, "mnida")
{
  if EndsWith(s, "po") {
    assert s[|s| - 2..] == "po";
    assert s[|s| - 1] == 'o';
  }
  if EndsWith(s, "desu") {
    assert s[|s| - 4..] == "desu";
    assert s[|s| - 1] == 'u';
  }
  if EndsWith(s, "masu") {
    assert s[|s| - 4..] == "masu";
    assert s[|s| - 1] == 'u';
  }
  if EndsWith(s, "mnida") {
    assert s[|s| - 5..] == "mnida";
    assert s[|s| - 1] == 'a';
  }
}

method SuffixThree(sentences: seq<string>) returns (results: seq<string>)
  requires forall i :: 0 <= i < |sentences| ==> ValidSentence(sentences[i])
  ensures results == ClassifyAll(sentences)
{
  results := [];
  for i := 0 to |sentences|
    invariant results == ClassifyAll(sentences[..i])
  {
    var s := sentences[i];
    assert ValidSentence(s);

    // Prove that valid sentences have length >= 1
    assert EndsWith(s, "po") || EndsWith(s, "desu") || EndsWith(s, "masu") || EndsWith(s, "mnida");
    assert |s| >= 2;

    LastCharDeterminesClassification(s);

    var last := s[|s| - 1];
    if last == 'o' {
      assert EndsWith(s, "po");
      results := results + ["FILIPINO"];
    } else if last == 'u' {
      assert EndsWith(s, "desu") || EndsWith(s, "masu");
      results := results + ["JAPANESE"];
    } else {
      assert EndsWith(s, "mnida");
      results := results + ["KOREAN"];
    }

    assert results == ClassifyAll(sentences[..i]) + [ClassifySentence(sentences[i])];
    assert sentences[..i+1] == sentences[..i] + [sentences[i]];
    assert sentences[..i+1][..|sentences[..i+1]|-1] == sentences[..i];
    ClassifyAllAppend(sentences[..i+1]);
  }
  assert sentences[..|sentences|] == sentences;
}
