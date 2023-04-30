extern "C" {
    fn get_attestation_report(buf: *mut u8, len: usize) -> i64;
}

fn main() {
    println!("Hello, world!");
    println!("trying to test attestation!!!");

    let mut vec = vec![0u8; 4096];
    let attestation_result = unsafe { get_attestation_report(vec.as_mut_ptr(), vec.len()) };

    if attestation_result != 0 {
        println!("attestation failed with {attestation_result:#x}");
    } else {
        println!("attestation passed.");
        println!("json response is {}", std::str::from_utf8(&vec).unwrap());
    }
}
