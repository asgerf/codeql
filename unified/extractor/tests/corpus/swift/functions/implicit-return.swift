func foo() -> String { "42" }
func explicitReturn() -> String { return "42" }
func multipleStatements() -> String {
  print("first")
  return "42"
}
func empty() {}
func declarationOnly() { let x = 42 }
func nestedBlock(_ condition: Bool) {
  if condition { print("not returned") }
}
func conditional(_ condition: Bool) -> String {
  if condition { "yes" } else { "no" }
}
struct ImplicitGetters {
  var implicitGetter: String { "42" }
  var explicitGetter: String { get { "42" } }
  var readWrite: String {
    get { "42" }
    set { print(newValue) }
  }
  init() { print("not returned") }
  deinit { print("not returned") }
}
let closure = { "42" }
let explicitClosure = { return "42" }
let multipleClosure = { print("first"); return "42" }
