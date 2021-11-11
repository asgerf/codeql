/**
 * Provides classes for contributing a model, or using the interpreted results
 * of a model represented as data.
 *
 * - Use the `ModelInput` module to contribute new models.
 * - Use the `ModelOutput` module to access the model results in terms of API nodes.
 *
 * The following tokens have a language-specific interpretation:
 *  - `Instance`: the value returned by a `new`-call to a function
 *  - `Awaited`: the value from a resolved promise
 *
 * A `(package, type)` tuple may refer to the exported type named `type` from the NPM package `package`.
 * For example, `(express, Request)` would match a parameter below due to the type annotation:
 * ```ts
 * import * as express from 'express';
 * export function handler(req: express.Request) { ... }
 * ```
 */

private import javascript
private import internal.Shared as Shared
import Shared::ModelInput as ModelInput
import Shared::ModelOutput as ModelOutput
