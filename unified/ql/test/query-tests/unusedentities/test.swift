func t1() -> Int {
    let a = 1 // $ Alert[unified/unused-variable]
    let b = 2
    return b
}

func t2() -> String {
    let a = 123 // $ SPURIOUS: Alert[unified/unused-variable]
    return "a = \(a)"
}
