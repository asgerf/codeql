private import CommonLayer

/** A spread element in an object literal, such as `{ ...x }` */
class ObjectSpreadElement extends SpreadElement {
  private Object object;

  ObjectSpreadElement() { this = object.getChild(_) }

  Object getObject() { result = object }
}

/** A spread element in an array literal, such as `[ ...x ]` */
class ArraySpreadElement extends SpreadElement {
  private Array array;

  ArraySpreadElement() { this = array.getChild(_) }

  Array getArray() { result = array }
}

/**
 * A rest pattern in an array pattern, such as `...rest` in `let [x, y, ...rest] = v`.
 */
class ArrayRestPattern extends RestPattern {
  private ArrayPattern pattern;

  ArrayRestPattern() { this = pattern.getChild(_) }

  ArrayPattern getArrayPattern() { result = pattern }
}

/**
 * A rest pattern in an object pattern, such as `...rest` in `let {x, y, ...rest} = v`.
 */
class ObjectRestPattern extends RestPattern {
  private ObjectPattern pattern;

  ObjectRestPattern() { this = pattern.getChild(_) }

  ObjectPattern getObjectPattern() { result = pattern }
}
