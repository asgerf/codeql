/** Provides a mechanism for resolving path strings to Ruby files. */

import codeql.files.FileSystem

/** Holds if `path` should be resolved relative to `baseFolder`. */
signature predicate needResolution(string path, Container baseFolder);

/** Module for resolving path strings relative to a given base folder. */
module PathResolver<needResolution/2 needRes> {
  private string getComponent(string path, int n) {
    needRes(path, _) and
    result = path.replaceAll("\\", "/").splitAt("/", n)
  }

  /** Gets the number of components in `path`. */
  int getNumComponent(string path) { result = strictcount(int i | exists(getComponent(path, i))) }

  /** Gets the file or folder referenced by the first `n` components of `path`. */
  Container resolveUpTo(string path, int n) {
    n = 0 and
    needRes(path, result)
    or
    exists(string component, Container prev |
      prev = resolveUpTo(path, n - 1) and
      component = getComponent(path, n - 1)
    |
      component = "." and
      result = prev
      or
      component = ".." and
      result = prev.getParentContainer()
      or
      not component = [".", ".."] and
      result = prev.getAChildContainer() and
      result.getBaseName() = component
      or
      // For the last step, optionally fill in the extension
      n = getNumComponent(path) and
      result = prev.getFile(component + ".rb")
    )
  }

  /** Gets the file or folder referenced by `path`. */
  Container resolve(string path) { result = resolveUpTo(path, getNumComponent(path)) }
}
