private import All

/**
 * A pair of key and value in an object literal, either `{ k: v }`, `{ [k]: v }`, or the shorthand `{ k }`.
 */
final class PairLike = PairLikeImpl;

abstract private class PairLikeImpl extends AstNode {
  /** Get the `k` in `{ k: v }` or in `{ [k]: v }` or in `{ k }`. */
  abstract AstNode getKey();

  /** Get the `v` in `{ k: v }` or in `{ v }`. */
  abstract AstNode getValue();

  /** Gets the object literal in which this pair appears. */
  Object getObject() { this = result.getChild(_) }
}

private class PairImpl extends PairLikeImpl instanceof Pair {
  override AstNode getKey() { result = Pair.super.getKey() }

  override AstNode getValue() { result = Pair.super.getValue() }
}

private class ShorthandPropertyIdentifierImpl extends PairLikeImpl instanceof ShorthandPropertyIdentifier
{
  override AstNode getKey() { result = this }

  override AstNode getValue() { result = this }
}
