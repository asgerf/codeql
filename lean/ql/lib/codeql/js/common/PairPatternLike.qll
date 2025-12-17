private import All

/**
 * A pair of key and value in an object pattern, either `{ k: v }` or the shorthand `{ k }`.
 */
final class PairPatternLike = PairPatternLikeImpl;

abstract private class PairPatternLikeImpl extends AstNode {
  /** Get the `k` in `{ k: v }` or in `{ k }`. */
  abstract AstNode getKey();

  /** Get the `v` in `{ k: v }` or in `{ v }`. */
  abstract AstNode getValue();

  /** Gets the object pattern in which this pair appears. */
  ObjectPattern getObjectPattern() { this = result.getChild(_) }
}

private class PairPatternImpl extends PairPatternLikeImpl instanceof PairPattern {
  override AstNode getKey() { result = PairPattern.super.getKey() }

  override AstNode getValue() { result = PairPattern.super.getValue() }
}

private class ShorthandPairPatternImpl extends PairPatternLikeImpl instanceof ShorthandPropertyIdentifierPattern
{
  override AstNode getKey() { result = this }

  override AstNode getValue() { result = this }
}
