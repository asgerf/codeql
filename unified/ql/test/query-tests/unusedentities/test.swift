func t1() -> Int {
    let a = 1 // $ Alert[unified/unused-variable]
    let b = 2
    return b
}
