use crate::types;

fn precondition(arg: types::A) {
    // verify that the argument(s) satisfy some precondition(s)
    // e.g., that `arg` doesn't have the taint tag
    // such verification should be flow-sensitive,
    // where the precondition is verified towards all possible call sites
}

fn reachibility() {
    // verify that the next line of code will be executed(reached) if no panic occurs    
    println!("reached!");
}
