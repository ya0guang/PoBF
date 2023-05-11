use clap::Parser;
use std::fs::File;
use std::io::Write;

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
#[clap(propagate_version = true)]
struct Args {
    /// Data sizes you want to run.
    #[arg(short, long, default_value_t = 1000)]
    len: usize,

    /// The output path.
    #[arg(short, long, default_value_t = String::from("output.bin"))]
    output_path: String,
}

fn main() {
    let args = Args::parse();
    let len = args.len;
    let output_path = args.output_path;

    // Open the file.
    print!("writing dummy data with length {len} to {output_path}...");
    let mut file = File::create(&output_path).unwrap();
    let foo = vec![0u8; len];
    // Write `foo` as u8 array into file.
    file.write_all(&foo).unwrap();
    println!("\t\tok");
}
