extern "C" {
    fn do_attest() -> i64;
}

fn main() {
    println!("Hello, world!");
    println!("trying to test attestation!!!");

    let attestation_result = unsafe { do_attest() };

    if attestation_result != 0 {
        println!("attestation failed with {attestation_result:#x}");
    } else {
        println!("attestation passed.");
    }
}
