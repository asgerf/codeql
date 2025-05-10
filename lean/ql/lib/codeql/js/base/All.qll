/**
 * The "base" layer contains code that is shared with the post-processing upgrade script (PostProcessing.ql).
 *
 * It should be kept as small as possible, while facilitating code reuse between the main CodeQL libraries and the post-processing script.
 *
 * This file shold re-export everything in the base layer.
 *
 * Note: It is not possible to import arbitrary files here, since upgrades currently can't import anything.
 * We special-case support for importing the files in the "base" layer by inlining them in the generated
 * upgrade script.
 */

import codeql.Locations
import codeql.js.base.GeneratedAst::JS
import codeql.js.base.LanguageBase
import codeql.js.base.OptionalChaining
