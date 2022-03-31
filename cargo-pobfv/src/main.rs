mod compiler;
mod ocall;
mod safety;

use clap::Parser;
use compiler::*;

#[derive(Parser, Debug)]
struct Args {
    /// Run all verifications forcely, ignoring potential errors
    #[clap(short, long, parse(from_occurrences))]
    all: u8,

    /// Verify that `unsafe` is not allowed in the source code files
    #[clap(short, long, parse(from_occurrences))]
    safety: u8,

    /// Verify that OCALLs cannot leak out sensitive data
    #[clap(short, long, parse(from_occurrences))]
    ocall: u8,

    /// Verfiy that the rust compiler can compile the source code
    #[clap(short, long, parse(from_occurrences))]
    compile: u8,

    /// Features to include
    #[clap(short, long)]
    features: Vec<String>,
}

fn main() {
    let mut args = Args::parse();

    for f in &args.features {
        println!("Get feature: {}", f);
    }

    if args.all > 0 {
        args.safety = 1;
        args.ocall = 1;
        args.compile = 1;
    }

    if
}
