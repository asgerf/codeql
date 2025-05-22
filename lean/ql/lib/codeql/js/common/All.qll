/**
 * The "common" layer contains most AST abstactions, local variable resolution, the definition of "content" as well as general utility code
 * that isn't needed in the post-processing upgrade script, and does not depend on control flow or dataflow.
 */

import codeql.js.base.All
import codeql.js.common.BinaryExprLike
import codeql.js.common.Callable
import codeql.js.common.LanguageCommonJS
import codeql.js.common.LogicalNot
import codeql.js.common.PairLike
import codeql.js.common.PairPatternLike
import codeql.js.common.PropAccess
import codeql.js.common.ShortCircuitingOperators
import codeql.js.common.SpreadAndRest
import codeql.js.common.UpdateExpressions
import codeql.js.common.Util
import codeql.js.common.ValueFilter
import codeql.js.common.Variables
