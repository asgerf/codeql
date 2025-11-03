signature predicate shouldHashSig(string s);

module MakeStringHash<shouldHashSig/1 shouldHash> {
  int getHash(string s, int n) {
    shouldHash(s) and
    n = 0 and
    result = 0
    or
    result = getHash(s, n - 1) * 31 + s.codePointAt(n - 1)
  }

  int getHash(string s) { result = getHash(s, s.length()) }
}

private module Debug {
  predicate testStrings(string s) { s = ["foo", "bar", "bazbaz"] }

  predicate getHash = MakeStringHash<testStrings/1>::getHash/1;
}
