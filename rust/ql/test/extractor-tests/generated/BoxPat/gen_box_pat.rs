// generated by codegen

fn test_box_pat() -> () {
    // A box pattern. For example:
    match x {
        box Option::Some(y) => y,
        box Option::None => 0,
    };
}
