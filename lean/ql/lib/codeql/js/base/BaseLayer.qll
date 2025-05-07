/**
 * The "base" layer contains code that is shared with the post-processing upgrade script (PostProcessing.qll).
 *
 * It should be kept as small as possible, while facilitating code reuse between the main CodeQL libraries and the post-processing script.
 *
 * This file shold re-export everything in the base layer except PostProcessing.qll.
 *
 * Note: It is not possible to import arbitrary files here, since upgrades currently can't import anything.
 * We special-case support for importing the files in the "base" layer by inlining them in the generated
 * upgrade script.
 */

import codeql.js.base.GeneratedAst::JS
import codeql.js.base.Conditions
import codeql.js.base.LeftHandValues
import codeql.js.base.OptionalChaining
