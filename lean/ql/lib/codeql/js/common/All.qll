/**
 * The "common" layer contains most AST abstactions, the definition of "content" as well as general utility code
 * that isn't needed in the post-processing upgrade script, and does not depend on control flow or dataflow.
 */

import codeql.js.base.All
import codeql.js.common.BinaryExprLike
import codeql.js.common.CfgScope
import codeql.js.common.Contents
import codeql.js.common.Function
import codeql.js.common.LanguageCommon
import codeql.js.common.LogicalNot
import codeql.js.common.PropAccess
import codeql.js.common.SpreadAndRest
import codeql.js.common.ShortCircuitingOperators
import codeql.js.common.UpdateExpressions
import codeql.js.common.Util
import codeql.js.common.ValueFilter
import codeql.js.common.Variables
