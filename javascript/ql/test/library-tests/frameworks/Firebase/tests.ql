import javascript

query predicate firebaseRef(DataFlow::SourceNode ref) { ref = Firebase::Database::ref().track() }

query predicate firebaseSnapshot(DataFlow::SourceNode snap) { snap = Firebase::snapshot().track() }

query predicate firebaseVal(Firebase::FirebaseVal val) { any() }

query predicate requestInputAccess(Http::RequestInputAccess acc) { any() }

query predicate responseSendArgument(Http::ResponseSendArgument send) { any() }

query predicate routeHandler(Http::RouteHandler handler) { any() }
